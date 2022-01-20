{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
module LiquidSol.Solidity.Inliner
  ( resolveTypeIdents
  , constPartialEval
  , expandForLoops
  , functionHasBytes
  , functionHasAsm
  , inlineEnums
  , inlineFunctions
  , inlineModifiers
  , moveInitAssignments
  , resolveInheritance
  , varDeclHasBytes
  , module LiquidSol.Solidity.Preprocess.Libraries) where

import Control.Applicative (Alternative((<|>)))
import Control.Monad
import Control.Monad.Extra (fromMaybeM, findM)
import Data.Either (partitionEithers)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe (listToMaybe, catMaybes)
import Data.Text (Text)
import qualified Data.Text as Text
import Prelude hiding (head)

import LiquidSol.Solidity.ContextMonad
import LiquidSol.Solidity.Preprocess.Common
import LiquidSol.Solidity.Preprocess.Libraries
import LiquidSol.Solidity.Syntax
import LiquidSol.Util.Unsafe

-- | Resolve type information for expressions in each contract.
resolveTypeIdents :: SourceCtx -> SourceCtx
resolveTypeIdents = snd <$> runContext go
  where
    go = do
      contracts <- getsContext srcCtx_contracts
      -- Construct default scope
      let defScope = HashMap.fromList [(contract_name c, r) | (r, c) <- HashMap.toList contracts]

      -- Collect library structs
      let collectStructs prefix s cbref = getsContext (lookupRef cbref) >>= \case
            CStruct n _ -> pure $ HashMap.insert (prefix <> n) (asNodeRef cbref) s
            _ -> pure s
      let foldLibs scope c = case contract_kind c of
            SolLibraryKind -> foldM (collectStructs (contract_name c <> ".")) scope (contract_body c)
            _ -> pure scope
      libScope <- foldM foldLibs defScope contracts

      -- Replace type info in expressions of each contract
      forM_ contracts $ \c -> do
        let cprefix = contract_name c <> "."
        scope <- foldM (collectStructs "") libScope (contract_body c) >>=
                   \s' -> foldM (collectStructs cprefix) s' (contract_body c)
        forM_ (contract_body c) $ \cbref -> do
          cb <- getsContext (lookupRef cbref)
          cb' <- case cb of
            fun@CFun{cfun_body=body, cfun_mods=mods} -> do
              mods' <- forM mods $ \(r, es) -> (r,) <$> traverse (replaceExprM (visitExpr scope)) es
              body' <- traverse (replaceStmtM (visitExpr scope) (visitStmt scope)) body
              pure fun{cfun_body=body', cfun_mods=mods'}
            CMod name body -> do
              body' <- replaceStmtM (visitExpr scope) (visitStmt scope) body
              pure (CMod name body')
            CStateVar vdref -> do
              visitVarDecl scope vdref
              vd <- getsContext (lookupRef vdref)
              forM_ (varDecl_value vd) (replaceExprM (visitExpr scope))
              pure cb
            _ -> pure cb
          modifyContext (updateRef cbref cb')
      pure ()

    visitVarDecl :: Monad m => HashMap Text NodeRef -> VarDeclRef -> ContextT m ()
    visitVarDecl scope vdref = do
      vd <- getsContext (lookupRef vdref)
      let vd' = vd{varDecl_type = replaceTypes scope (varDecl_type vd)}
      modifyContext (updateRef vdref vd')

    visitStmt :: Monad m => HashMap Text NodeRef -> StmtRef -> SolStmt -> ContextT m SolStmt
    visitStmt scope _ = \case
      s@(SolStmtVarDecl vdrefs _) -> do
        forM_ vdrefs (visitVarDecl scope)
        pure s
      s -> pure s

    visitExpr :: Monad m => HashMap Text NodeRef -> ExprRef -> SolExpr -> ContextT m SolExpr
    visitExpr scope eref e = do
      e' <- case e of
        SolExprIdent n _
          | Just r <- HashMap.lookup n scope -> do
              pure (SolExprIdent n r)
        SolExprBinaryOp op e1 e2 ty -> pure $ SolExprBinaryOp op e1 e2 (replaceTypes scope ty)
        SolExprAssign op e1 e2 ty -> pure $ SolExprAssign op e1 e2 (replaceTypes scope ty)
        _ -> pure e
      getsContext (HashMap.lookup eref . srcCtx_exprTypes) >>= \case
        Just ty ->
          modifyContext (\ctx -> ctx{srcCtx_exprTypes = HashMap.insert eref (replaceTypes scope ty) (srcCtx_exprTypes ctx)})
        _ -> pure ()
      pure e'

    replaceTypes :: HashMap Text NodeRef -> SolType -> SolType
    replaceTypes scope = \case
      SolTyArr t msz -> SolTyArr (replaceTypes scope t) msz
      SolTyMapping t1 t2 -> SolTyMapping (replaceTypes scope t1) (replaceTypes scope t2)
      SolTyTuple ts -> SolTyTuple (replaceTypes scope <$> ts)
      SolTyUser _ n | Just r <- HashMap.lookup n scope -> SolTyUser r n
      t -> t

-- | Move initialization assignments from contract body into constructor.
-- Inserts constructor if necessary.
moveInitAssignments :: SourceCtx -> SourceCtx
moveInitAssignments = snd . runContext go
  where
    findCtor cbodies = findM (fmap matchCtor . getsContext . lookupRef) cbodies
    matchCtor = \case
      CFun{cfun_isCtor=True} -> True
      _ -> False
    mkCtor cref = do
      body <- createNode (SolStmtBlock [])
      let f = CFun{ cfun_name="", cfun_args=[], cfun_rets=[], cfun_mods=[]
                    , cfun_isCtor=True, cfun_body=Just body, cfun_vis=VisPublic
                    , cfun_mut=MutNone }
      cb <- createNode f
      fakeLoc <- getsContext ((\l -> l{srcLoc_len=0}) . (`hmUnsafeLookup` cref) . srcCtx_locs)
      modifyContext (\ctx ->
                       ctx{srcCtx_locs
                             = HashMap.insert (asNodeRef body) fakeLoc
                             . HashMap.insert (asNodeRef cb) fakeLoc
                             $ srcCtx_locs ctx})
      pure cb
    go = do
      contracts <- getsContext (HashMap.toList . srcCtx_contracts)
      forM_ (filter ((/= SolLibraryKind) . contract_kind . snd) contracts) $ \(cref, ct) -> do
        ctorRef <- fromMaybeM (mkCtor cref) (findCtor (contract_body ct))
        when (ctorRef `notElem` contract_body ct) $
          modifyContext (updateRef (unsafeCastTypedRef cref) ct{contract_body=ctorRef : contract_body ct})
        -- Find top-level variable assignments
        assigns <- fmap catMaybes $ forM (contract_body ct) $ \cbref -> do
          ctx <- getContext
          case lookupRef cbref ctx of
            CStateVar vdref@(flip lookupRef ctx -> vd)
              | Just eref <- varDecl_value vd -> do
                modifyContext (updateRef vdref vd{varDecl_value = Nothing})
                pure (Just (vdref, vd, eref))
            _ -> pure Nothing
        -- Insert variable assignments into ctor
        getsContext (lookupRef ctorRef) >>= \case
          f@CFun{cfun_body=Just bodyRef} -> do
            bodyRef' <- copyNode bodyRef
            stmts <- forM assigns $ \(vdref, SolVarDecl{varDecl_name=x, varDecl_type=ty}, eref) -> do
              ident <- copyNode eref
              modifyContext (updateRef ident (SolExprIdent x (asNodeRef vdref)))
              modifyContext (\ctx -> ctx{srcCtx_exprTypes = HashMap.insert ident ty (srcCtx_exprTypes ctx)})
              easgn <- copyNode eref
              modifyContext (updateRef easgn (SolExprAssign "=" ident eref ty))
              sasgn <- copyNode bodyRef
              modifyContext (updateRef sasgn (SolStmtExpr easgn))
              pure sasgn
            modifyContext (updateRef bodyRef' (SolStmtBlock (stmts <> [bodyRef])))
            modifyContext (updateRef ctorRef f{cfun_body=Just bodyRef'})
          _ -> undefined

-- | Inline inherited variables and methods, removing all abstract contracts.
resolveInheritance :: SourceCtx -> SourceCtx
resolveInheritance = snd . runContext go
  where
    splitLibs p@(_, c) = case contract_kind c of
      SolContractKind -> Right p
      _ -> Left p
    go = do
      contracts0 <- getsContext (HashMap.toList . srcCtx_contracts)
      let (libs, contracts) = partitionEithers (splitLibs <$> contracts0)
      (contracts', toEdit) <- fmap unzip $ forM contracts $ \(cref, ct) -> do
        -- Find base contracts. Note that default order is this->parent->grandparent.
        bases <- traverse (getsContext . lookupRef) (contract_bases ct)
        -- Find all definitions not present in base contract.
        defines <- traverse (\b -> getsContext (Map.fromList . getDefined b)) bases
        let notDefined = mconcat (Map.keysSet <$> tail defines)
              `Set.difference` Map.keysSet (head defines)
            lookupInherit (defMap:defMapRest) name = case Map.lookup name defMap of
              Just ref -> ref
              Nothing -> lookupInherit defMapRest name
            lookupInherit _ _ = undefined
            inherited = lookupInherit defines <$> Set.toList notDefined
        inherited' <- if contract_full ct then traverse deepCopyCbody inherited else pure []

        -- Find constructor of this contract
        thisCtorM <- filterCtor (contract_body ct)
        -- Find constructor of parent contracts
        let getParentCtor (cr, c) = (cr,) <$> filterCtor (contract_body c)
        parentCtors <- traverse getParentCtor (reverse (tail (contract_bases ct `zip` bases)))

        -- Create inlining edits
        -- Replace the constructor only if there is at least one parent constructor
        let mkCtor = \case
              Just r -> pure r
              Nothing -> error "constructor does not exist"
            -- Inline parent constructors
            inlineCtors r = getsContext (lookupRef r) >>= \case
              f@CFun{cfun_mods=argList, cfun_body=Just bodyRef, cfun_isCtor=True} -> do
                let argMap = HashMap.fromList argList
                -- Create inlined copy of parent constructor code
                parentCtorCalls <- forM parentCtors $ \(pcref, pctorRefM) -> do
                  -- Inline parent constructor body if it exists
                  let args = HashMap.lookupDefault [] (asNodeRef pcref) argMap
                  forM pctorRefM (\pctorRef -> inlineFunction pctorRef args [])
                bodyRef' <- copyNode bodyRef
                let newBody = SolStmtBlock (catMaybes parentCtorCalls <> [bodyRef])
                modifyContext (updateRef bodyRef' newBody)
                -- But we don't want to modify the function during the inlining, so defer to later.
                pure (r, f, bodyRef')
              _ -> undefined
        -- If this has no constructor, insert an empty constructor.
        thisCtor <- mkCtor thisCtorM
        -- Generate new ctor body with parent ctors inlined
        toEdit <- inlineCtors thisCtor
        let body' = inherited' <> contract_body ct
        pure ((cref, ct{contract_body = body'}), toEdit)
      -- Apply inlining edits
      forM_ toEdit $ \(r, f, bodyRef') -> case f of
        CFun{} -> modifyContext (updateRef r f{cfun_body=Just bodyRef'})
        _ -> undefined
      -- Update contract bodies
      modifyContext (\ctx -> ctx{srcCtx_contracts = HashMap.fromList (libs <> contracts')})
    getDefined ct ctx = catMaybes (addDefine ctx <$> contract_body ct)
    addDefine ctx ref = case lookupRef ref ctx of
      CStateVar vdRef | SolVarDecl{varDecl_name=name} <- lookupRef vdRef ctx -> Just (name, ref)
      -- CFun{cfun_name=name, cfun_body=(Just _), cfun_isCtor=False} -> Just (name, ref)
      CStruct name _ -> Just (name, ref)
      _ -> Nothing
    -- Capture the body ref as well so that we can use it
    filterCtor [] = pure Nothing
    filterCtor (r:rs) = getsContext (lookupRef r) >>= \case
      CFun{cfun_isCtor=True} -> pure $ Just r
      _ -> filterCtor rs

-- | Inline internal function calls.
inlineFunctions :: SourceCtx -> SourceCtx
inlineFunctions = snd . runContext go
  where
    go = do
      contracts <- getsContext (HashMap.toList . srcCtx_contracts)
      forM_ contracts $ \(_, ct) -> do
        forM_ (contract_body ct) $ \cbref -> getsContext (lookupRef cbref) >>= \case
          f@CFun{cfun_body=body} -> do
            body' <- traverse (replaceStmtM (\_ e -> pure e) (substCalls (contract_body ct))) body
            modifyContext (updateRef cbref f{cfun_body=body'})
          _ -> pure ()
    hasReturn sref ctx = case lookupRef sref ctx of
      SolStmtBlock stmts -> any (flip hasReturn ctx) stmts
      SolStmtWhile _ stmt -> hasReturn stmt ctx
      SolStmtIf _ stmt1 mStmt2 ->
        hasReturn stmt1 ctx || maybe False (flip hasReturn ctx) mStmt2
      SolStmtReturn{} -> True
      _ -> False
    substCalls functionBody _ s = do
      ctx <- getContext
      case s of
        SolStmtExpr eref
          | SolExprFunCall ef eargs <- lookupRef eref ctx
          , SolExprIdent _ fref <- lookupRef ef ctx
          , fref `elem` (asNodeRef <$> functionBody)
          , Just CFun{cfun_vis=vis, cfun_args=funArgs, cfun_body=Just fbody, cfun_isCtor=False} <- tryLookupRef fref ctx
          , vis == VisInternal || vis == VisPrivate
          , not (hasReturn fbody ctx) -> do
            -- First, convert all arguments to ANF form
            (anfStmts, eargs') <- fmap unzip $ forM (eargs `zip` funArgs) $ \(aref, fargRef) -> do
              atype <- varDecl_type <$> getsContext (lookupRef fargRef)
              anfLiftExpression atype aref
            -- Now we inline the function.
            sref' <- inlineFunction (unsafeCastTypedRef fref) eargs' []
            pure $ SolStmtBlock (catMaybes anfStmts <> [sref'])
        _ -> pure s


-- | Inline enum definitions
inlineEnums :: SourceCtx -> SourceCtx
inlineEnums ctx0 =
  let finalCtx = foldl goInline ctx0 contracts in
    finalCtx
      { srcCtx_exprs = HashMap.map inlineExpr (srcCtx_exprs finalCtx)
      , srcCtx_varDecls = HashMap.map inlineVarDecl (srcCtx_varDecls finalCtx)
      }
  where
    contracts = unsafeCastTypedRef <$> HashMap.keys (srcCtx_contracts ctx0)
    -- First, collect definitions
    getEnumDef cbref = case lookupRef cbref ctx0 of
      CEnum _ values -> Just (asNodeRef cbref, Map.fromList (values `zip` [(0 :: Integer)..]))
      _ -> Nothing
    enumDefs = Map.fromList . catMaybes $ fmap getEnumDef
      [cbRef | ct <- flip lookupRef ctx0 <$> contracts , cbRef <- contract_body ct]
    -- Convert all enum types into uint
    replaceType = \case
      SolTyUser cbref _ | Map.member cbref enumDefs -> SolTyElem "uint"
      SolTyArr t1 msz -> SolTyArr (replaceType t1) msz
      SolTyMapping t1 t2 -> SolTyMapping (replaceType t1) (replaceType t2)
      t -> t
    inlineVarDecl vd = vd{varDecl_type = replaceType (varDecl_type vd)}
    -- Replace enum members with constants
    inlineExpr = \case
      SolExprMember eref val _
        | SolExprIdent _ declRef <- lookupRef eref ctx0
        , Just vals <- Map.lookup declRef enumDefs ->
        let intValue = vals `unsafeLookup` val in
          SolExprLit (SolLitInt intValue)
      e -> e
    -- Remove enum definitions from contract bodies
    inlineCbody ctx cbref = (cbref,) <$> case lookupRef cbref ctx of
      CEnum{} -> Nothing
      cb -> Just cb
    -- Inline in contract bodies
    goInline :: SourceCtx -> ContractRef -> SourceCtx
    goInline ctx cref =
      let
        ct = lookupRef cref ctx0
        cbodies = catMaybes (inlineCbody ctx0 <$> contract_body ct)
        ct' = ct
          { contract_body = fst <$> cbodies }
      in
        ctx{ srcCtx_contracts = HashMap.insert (asNodeRef cref) ct' (srcCtx_contracts ctx)
           , srcCtx_cbody = HashMap.fromList [(asNodeRef r, cb) | (r, cb) <- cbodies] <> srcCtx_cbody ctx }

-- | Replaces all for loops with equivalent while loops
expandForLoops :: SourceCtx -> SourceCtx
expandForLoops ctxInit = finalCtx{srcCtx_stmts = finalChanges <> srcCtx_stmts ctxInit}
  where
    (finalCtx, finalChanges) = foldl go (ctxInit, HashMap.empty) (HashMap.toList (srcCtx_stmts ctxInit))
    go (ctx, changes) (sref, stmt) = case stmt of
      SolStmtFor initStmt cond (afterStmt, _) bodyRef ->
        -- Convert as follows:
        --     for[a] (init[b]; cond[c]; after[d]) body[e]
        -- ==>
        --     [a]{ init[b]; while[fresh] (cond[c]) [fresh]{ body[e]; after[d] } }
        let
          (bodyRef', ctx') = runContext (copyNode (unsafeCastTypedRef sref)) ctx
          (whileRef, newCtx) = runContext (copyNode bodyRef) ctx'
          newBody = SolStmtBlock [bodyRef, afterStmt]
          whileLoop = SolStmtWhile cond bodyRef'
          newChanges
            = HashMap.insert sref (SolStmtBlock [initStmt, whileRef])
            . HashMap.insert (asNodeRef whileRef) whileLoop
            . HashMap.insert (asNodeRef bodyRef') newBody
            $ changes
        in
          (newCtx, newChanges)
      _ -> (ctx, changes)


inlineModifiers :: SourceCtx -> SourceCtx
inlineModifiers ctx0 = finalCtx
  where
    finalCtx = ctx'{ srcCtx_contracts = HashMap.map removeModifiers (srcCtx_contracts ctx0) }
    removeModifiers ct =
      ct{contract_body = filter isNotModifier (contract_body ct)}
    isNotModifier cbref = case lookupRef cbref ctx0 of
      CMod{} -> False
      _ -> True
    ctx' = runInline ctx0 (unsafeCastTypedRef <$> HashMap.keys (srcCtx_cbody ctx0))
    runInline ctx [] = ctx
    runInline ctx (cbref:rest) = case lookupRef cbref ctx of
      fun@CFun{cfun_body=Just body, cfun_isCtor=False} ->
        let
          -- TODO: Handle modifiers with arguments
          mods = [mbody |
                  (flip tryLookupRef ctx0 -> Just (CMod _ mbody), []) <- cfun_mods fun]
          (body', newCtx) = foldl modSub (body, ctx) mods
          fun' = fun{cfun_body = Just body', cfun_mods = mempty}
          newCtx' = newCtx{srcCtx_cbody = HashMap.insert (asNodeRef cbref) fun' (srcCtx_cbody ctx) }
        in
          runInline newCtx' rest
      _ -> runInline ctx rest
    modSub :: (StmtRef, SourceCtx) -> StmtRef -> (StmtRef, SourceCtx)
    modSub (funBody, ctx) sref =
      let (modBody, ctxA) = runContext (deepCopyStmt sref) ctx
          sph = fromJust (findPlaceholder ctxA modBody) in
        (modBody, updateRef sph (lookupRef funBody ctxA) ctxA)
    findPlaceholder ctx sref = case lookupRef sref ctx of
      SolStmtPlaceholder -> Just sref
      SolStmtBlock stmts -> listToMaybe (catMaybes (findPlaceholder ctx <$> stmts))
      SolStmtIf _ b1 b2 -> findPlaceholder ctx b1 <|> (b2 >>= findPlaceholder ctx)
      SolStmtWhile{} -> error "inlineModifiers: while inside modifier not supported"
      SolStmtReturn{} -> error "inlineModifiers: return inside modifier not supported"
      _ -> Nothing

-- | If a variable declaration is for some variable of type bytes*
varDeclHasBytes :: VarDeclRef -> SourceCtx -> Bool
varDeclHasBytes vdr ctx =
  let vd = lookupRef vdr ctx in
    case varDecl_type vd of
      SolTyElem t | Text.isPrefixOf "bytes" t -> True
      _ -> False

-- | If a statement contains bytes in its body
functionHasBytes :: StmtRef -> SourceCtx -> Bool
functionHasBytes sref ctx = case lookupRef sref ctx of
  SolStmtVarDecl vds _ -> any (flip varDeclHasBytes ctx) vds
  SolStmtBlock stmts -> any (flip functionHasBytes ctx) stmts
  SolStmtWhile _ stmt -> functionHasBytes stmt ctx
  SolStmtIf _ stmt1 mStmt2 ->
    functionHasBytes stmt1 ctx || maybe False (flip functionHasBytes ctx) mStmt2
  _ -> False

-- | If a statement contains inline assembly in its body
functionHasAsm :: StmtRef -> SourceCtx -> Bool
functionHasAsm sref ctx = case lookupRef sref ctx of
  SolStmtBlock stmts -> any (flip functionHasAsm ctx) stmts
  SolStmtWhile _ stmt -> functionHasAsm stmt ctx
  SolStmtIf _ stmt1 mStmt2 ->
    functionHasAsm stmt1 ctx || maybe False (flip functionHasAsm ctx) mStmt2
  SolStmtAsm{} -> True
  _ -> False

-- | Partially evaluate constant expressions
constPartialEval :: SourceCtx -> SourceCtx
constPartialEval = snd . runContext go
  where
    ops = Map.fromList [("**", (^)), ("+", (+)), ("-", (-)), ("*", (*))]
    goEvalExpr _ = \case
      e@(SolExprBinaryOp op e1 e2 _) | Just f <- Map.lookup op ops -> do
        ctx <- getContext
        if | SolExprLit (SolLitInt x) <- lookupRef e1 ctx
           , SolExprLit (SolLitInt y) <- lookupRef e2 ctx ->
             pure $ SolExprLit (SolLitInt (f x y))
           | otherwise -> pure e
      e@(SolExprTypeConvert (SolTyElem t) vref) | "uint" `Text.isPrefixOf` t ->
        getsContext (lookupRef vref) >>= \case
          v@(SolExprLit (SolLitInt _)) -> pure v
          _ -> pure e
      e -> pure e
    evalExpr = replaceExprM goEvalExpr
    varDeclEval vd =
      let me = traverse evalExpr (varDecl_value vd) in
        fmap (\e' -> vd{varDecl_value = e'}) me
    go = do
      contracts <- getsContext srcCtx_contracts
      forM_ contracts $ \c -> do
        forM_ (contract_body c) $ \cbref -> do
          cb <- getsContext (lookupRef cbref)
          case cb of
            CStateVar vdref -> do
              vd <- getsContext (lookupRef vdref)
              _ <- varDeclEval vd
              pure ()
            f@CFun{cfun_body=body} -> do
              body' <- traverse (replaceStmtM goEvalExpr (\_ -> pure)) body
              modifyContext (updateRef cbref f{cfun_body=body'})
            _ -> pure ()
      pure ()
