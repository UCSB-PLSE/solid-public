{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
module LiquidSol.ConsGen
  ( ConsGenM, runConsGen, evalConsGen
  , freshVar
  , consGen, consGenDecl, consGenBlock, consGenStmt, consGenExpr ) where

import Data.Text (Text)
import Data.Maybe (fromMaybe, catMaybes)
import Data.Functor.Identity (runIdentity)
import Control.Monad.RWS.Strict
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import LiquidSol.AstAnalysis (scanAscriptions)
import LiquidSol.Syntax
import LiquidSol.LiquidTypes
import LiquidSol.Logic
import LiquidSol.Util.Fresh
import qualified LiquidSol.Util.Stream as Stream
import LiquidSol.Util.Unsafe (unsafeLookup, fromJust)
import LiquidSol.Solidity.Types
import qualified LiquidSol.AggProps as Agg

data CgState = CgState
  { stLocalEnv :: LiLocalEnv
  , stGlobalEnv :: LiGlobalEnv
  , stDelta :: LiDelta
  , stVarSkels :: Map Text (LiLocalEnv, LIRType)
  , -- | Set of unfetched locations in constructor, to determine when to
    -- zero-initialize
    stCtorFetch :: Set Loc
  , -- | Type ascriptions
    stAscriptions :: Map Text (RType Pred)
  , -- | Values returned with return statement
    stReturnValues :: [(LiLocalEnv, [Expr])]
  , -- | The liquid type variable of the contract invariant
    stContractInv :: Int
  , -- | Function pre/post conditions
    stFunctionSig :: Map Text (Int, Int)
  , -- | Inferred predicates
    stInfPreds :: Map Int InfPred
  , -- | Current function info (for diagnostic purposes)
    stCurFun :: Maybe Text
  , -- | Current statement info (for diagnostic purposes)
    stCurSrcLoc :: Maybe SrcLoc
  }
  deriving (Show)

cgStateEmpty :: CgState
cgStateEmpty = CgState { stLocalEnv = localEnvEmpty
                       , stGlobalEnv = globalEnvEmpty
                       , stDelta = deltaEmpty
                       , stVarSkels = Map.empty
                       , stCtorFetch = Set.empty
                       , stAscriptions = Map.empty
                       , stReturnValues = mempty
                       , stContractInv = 0
                       , stFunctionSig = mempty
                       , stInfPreds = mempty
                       , stCurFun = Nothing
                       , stCurSrcLoc = Nothing }

newtype ConsGenM a = ConsGenM { runConsGen :: RWST () [LiJudgment] CgState (Fresh Int) a }
  deriving ( Functor, Applicative, Monad
           , MonadState CgState
           , MonadWriter [LiJudgment])

freshVar :: ConsGenM LIPred
freshVar = ConsGenM . lift . fmap (flip LIVar mempty) $ nextFresh

getEnv :: ConsGenM LiLocalEnv
getEnv = gets stLocalEnv

putEnv :: LiLocalEnv -> ConsGenM ()
putEnv env = modify (\st -> st { stLocalEnv = env })

modifyEnv :: (LiLocalEnv -> LiLocalEnv) -> ConsGenM ()
modifyEnv f = modify (\st -> st { stLocalEnv = f (stLocalEnv st) })

evalConsGen :: ConsGenM a -> (a, [LiJudgment], Map Int InfPred)
evalConsGen m =
  -- start at 1 since 0 is the contract invariant
  let freshVarStream = Stream.unfold (+1) 1
      freshM = runRWST (runConsGen m) () cgStateEmpty in
    (\(a, st, cons) -> (a, cons, stInfPreds st)) . runIdentity . evalFreshT freshVarStream $ freshM

-- | Instantiate constraints for global environment
consGenDelta :: [Decl ()] -> ConsGenM LiDelta
consGenDelta decls = do
  let mkTrue (x, t) = (x, fmap (const (predicate PTrue)) t)
  -- Instantiate function pre/post conditions
  (structs, funs) <- fmap unzip $ forM decls $ \case
    DFun{dfun_name=name, dfun_args=args, dfun_res=res, dfun_mut=mut} -> do
      let emptyVars = localEnvVarAssoc (localEnvEmpty :: LocalEnv ())
      (liPre, _) <- mkInfPred emptyVars (Left args) InfPredOther
      (liPost, _) <- mkInfPred emptyVars (Left (args <> res)) InfPredOther
      modify (\st -> st{stFunctionSig = Map.insert name (liPre, liPost) (stFunctionSig st)})
      pure (Nothing, Just (name, (mkTrue <$> args, mkTrue <$> res, mut)))
    DStruct name flds -> pure (Just (name, mkTrue <$> flds), Nothing)
    _ -> pure (Nothing, Nothing)
  pure $ Delta
    { delta_structs = Map.fromList (catMaybes structs)
    , delta_funs = Map.fromList (catMaybes funs) }

-- | Generate constraints for the contract. Returns the contract with updated
-- type information.
consGen :: Contract () -> ConsGenM (Contract LIPred, LiGlobalEnv)
consGen (Contract name decls) = do
  let stoAscribe = catMaybes $ flip fmap decls $ \case
        DAnnot (AAscribe x t) -> Just (x, t)
        _ -> Nothing
  delta' <- consGenDelta decls
  modify (\st -> st{ stDelta=delta'
                   , stAscriptions = Map.fromList [(x, predicate <$> t) | (x, t) <- stoAscribe] })
  decls' <- traverse consGenDecl decls
  gEnv <- gets stGlobalEnv
  pure (Contract name decls', gEnv)

{-
instantiateRType :: UType -> ConsGenM LIRType
instantiateRType (RType v t _) = RType v <$> instantiateSkel t <*> li
  where
    li = case t of
      TyStruct{} -> pure $ predicate PTrue
      _ -> freshVar

instantiateSkel :: USkel -> ConsGenM LISkel
instantiateSkel = \case
  TyInt i -> pure (TyInt i)
  TyBool -> pure TyBool
  TyUnit -> pure TyBool
  TyByte -> pure TyByte
  TyAddress -> pure TyAddress
  TyFunc x t1 t2 -> TyFunc x <$> instantiateRType t1 <*> instantiateRType t2
  TyMapping t1 t2 -> TyMapping <$> instantiateSkel t1 <*> instantiateSkel t2
  TyArray t1 msz -> TyArray <$> instantiateSkel t1 <*> pure msz
  TyStruct n _ ->
    gets (deltaResolveSkel (TyStruct n []) . stDelta) >>= \case
      Just (TyStruct _ flds) ->
        TyStruct n <$> mapM (\(x, t) -> (x,) <$> instantiateRType (const () <$> t)) flds
      _ -> undefined
-}

-- | Create a fresh inferred predicate
mkInfPred :: [(Text, UType)] -> Either [(Text, UType)] [Loc] -> InfPredType -> ConsGenM (Int, InfPred)
mkInfPred vars params ipType = do
  li <- ConsGenM $ lift nextFresh
  let inf = InfPred vars params ipType
  modify (\st -> st{stInfPreds = Map.insert li inf (stInfPreds st)})
  pure (li, inf)

mkPhiVar :: Int -> PendingSub -> Text -> RType () -> ConsGenM LIRType
mkPhiVar li psub x (RType v ty ()) = do
  env <- getEnv
  let template = RType v (fmap (const (predicate PTrue)) ty) (LIVar li psub)
  modifyEnv (localEnvUpdateVar x template)
  modify (\st -> st { stVarSkels = Map.insert x (env, template) (stVarSkels st) })
  pure template

genInvCons :: LocalEnv LIPred -> Int -> Map Text Expr -> PropTag -> ConsGenM ()
genInvCons env li vars tag = do
  let mkRtype = RType "v" TyBool
  let skelL = mkRtype (LIVar li psubEmpty{psubVars = Map.map exprToPred vars})
  emitCons env (mkRtype (predicate PTrue)) skelL tag

-- | Generate constraints for the declaration. Returns the declaration with
-- updated type information.
consGenDecl :: Decl () -> ConsGenM (Decl LIPred)
consGenDecl = \case
  DVar x ty exprM l -> do
    -- env <- getEnv
    template <- gets (Map.lookup x . stAscriptions) >>= \case
      Just s -> pure (predicate <$> s)
      Nothing -> do
        contractInv <- gets stContractInv
        let RType v skel () = ty
        skel' <- resolveSkel (shapeSkel skel)
        let ty' = RType v skel' (LIVar contractInv psubEmpty)
        pure ty'
    modify (\c -> c { stGlobalEnv = globalEnvUpdateLoc l x template (stGlobalEnv c) })
    pure (DVar x template exprM l)
  d@DFun { dfun_name = name, dfun_args = args, dfun_res = res, dfun_body = body, dfun_vis = vis } -> do
    modify (\st -> st{stCurFun = Just name })
    (args', res', body') <- consGenFun (Just name) vis args res body
    modify (\st -> st{stCurFun = Nothing })
    pure d{ dfun_args = args'
          , dfun_res = res'
          , dfun_body = body'  }
  d@DCtor { dctor_args = args, dctor_body = body } -> do
    locs <- gets (globalEnvLocSet . stGlobalEnv)
    modify (\c -> c { stCtorFetch = locs, stCurFun = Just "<constructor>" })
    (args', _, body') <- consGenFun Nothing VisExt args [] body
    modify (\c -> c { stCtorFetch = Set.empty, stCurFun = Nothing })
    pure d{ dctor_args = args', dctor_body = body' }
  DAnnot annot -> pure (DAnnot annot)
  DStruct { dsct_name=name, dsct_fields=flds} ->
    pure DStruct{dsct_name=name, dsct_fields=[(x, fmap (const (predicate PTrue)) t) | (x, t) <- flds]}
  where
    trueSkel = exprSkel TyBool (EConst (CBool True))
    consGenFun nameM vis args res body = do
      -- "Push" a new scope
      oldEnv <- getEnv
      modify (\st -> st{stGlobalEnv = globalEnvClearCheckout (stGlobalEnv st)})
      -- Subtype constraints on arguments
      let getSig name = gets ((`unsafeLookup` name) . stFunctionSig)
      let psubArgs = psubEmpty{psubVars = Map.fromList [(x, PVar x) | (x, _) <- args]}
      args' <- withAscriptionScope body $ forM args $ \(x, ty) -> do
        let RType v _ _ = ty
        case nameM of
          Just name -> do
            (liArg, _) <- getSig name
            xSkel <- mkPhiVar liArg (psubAddVar x (PVar v) psubArgs) x ty
            pure (x, xSkel)
          Nothing -> do
            let template = fmap (const (predicate PTrue)) ty
            modifyEnv (localEnvUpdateVar x template)
            env <- getEnv
            modify (\st -> st { stVarSkels = Map.insert x (env, template) (stVarSkels st) })
            pure (x, template)
      case vis of
        VisExt | Nothing <- nameM -> pure ()
        VisExt | Just name <- nameM -> do
          -- This function can be called from anywhere, so ensure nothing can be
          -- known about the arguments.
          (liArg, _) <- getSig name
          env <- getEnv
          emitCons
            (localEnvMap (const (predicate PTrue)) env)
            trueSkel
            (RType "v" TyBool (LIVar liArg psubArgs))
            PropNone
        VisInt ->
          -- Since this function is internal, we'll constrain the inferred
          -- precondition based on the function's call sites.
          pure ()

      (body', hasReturn) <- consGenBlock body
      -- Generate subtyping constraints on the final return values
      res' <- case nameM of
        Just name -> do
          (_, liRes) <- getSig name
          let resVars = args <> res
          let psubRes = psubArgs <> psubEmpty{psubVars = Map.fromList [(x, PVar x) | (x, _) <- resVars]}
          res' <- withAscriptionScope body $ forM res $ \(x, RType v bty ()) -> do
            let ty' = RType v (shapeSkel bty) (LIVar liRes psubRes)
            pure (x, ty')
          unless hasReturn $ getEnv >>= \env ->
            emitCons env trueSkel (RType "v" TyBool (LIVar liRes psubRes)) PropNone
          -- Generate subtyping constraints for values returned through a return statement
          gets stReturnValues >>= \retvals -> forM_ retvals $ \(env, es) -> do
            let psubResVars = Map.fromList [(x, exprToPred e) | ((x, _), e) <- res `zip` es]
                psubRes' = psubRes{psubVars = psubResVars <> psubVars psubRes}
            emitCons env trueSkel (RType "v" TyBool (LIVar liRes psubRes')) PropNone
          pure res'
        Nothing -> pure []
      -- Restore old scope
      putEnv oldEnv
      modify (\st -> st{ stGlobalEnv = globalEnvClearCheckout (stGlobalEnv st)
                       , stReturnValues = mempty })
      pure (args', res', body')

resolveSkel :: LISkel -> ConsGenM LISkel
resolveSkel skel = gets (fromJust . deltaResolveSkel skel . stDelta)

withAscriptionScope :: Block () -> ConsGenM a -> ConsGenM a
withAscriptionScope b m = do
  let asc = scanAscriptions b
  oldAsc <- gets stAscriptions
  modify (\st -> st{stAscriptions = Map.map (fmap predicate) (Map.fromList asc)})
  a <- m
  modify (\st -> st{stAscriptions = oldAsc})
  pure a

-- | Generate constraints for the block.
consGenBlock :: Block () -> ConsGenM (Block LIPred, Bool)
consGenBlock b = (,earlyStop) <$> withAscriptionScope b (traverse go stmts)
  where
    (stmts, earlyStop) = takeUntilReturn b
    go (loc, s) = do
      modify (\st -> st{ stCurSrcLoc = Just loc })
      s' <- consGenStmt s
      modify (\st -> st{ stCurSrcLoc = Nothing })
      pure (loc, s')

-- | Generate constraints for the statement. Returns the statement with updated
-- type information.
consGenStmt :: Stmt () -> ConsGenM (Stmt LIPred)
consGenStmt = \case
  SDecl x ty exprM -> do
    expr <- maybe (EConst . zeroValue <$> resolveSkel (shapeSkel (rtypeSkel ty))) pure exprM
    env <- getEnv
    skel <- consGenExpr expr
    modifyEnv (localEnvUpdateVar x skel)
    modify (\st -> st { stVarSkels = Map.insert x (env, skel) (stVarSkels st) })
    pure (SDecl x skel exprM)
  SIf phi e sThen sElse -> do
    let cond = exprToPred e
    _ <- consGenExpr e
    -- Generate then branch constraints
    env <- getEnv
    modifyEnv (localEnvAddPred cond)
    (sThen', returnThen) <- consGenBlock sThen
    thenEnv <- getEnv
    putEnv env
    -- Generate else branch constraints
    modifyEnv (localEnvAddPred (PNot cond))
    (sElse', returnElse) <- consGenBlock sElse
    elseEnv <- getEnv
    putEnv env
    -- Generate phi node constraint
    (li, _) <- mkInfPred (localEnvVarAssoc env) (Left [(x, ty) | (x, ty, _) <- phi]) InfPredOther
    let declPsub = psubEmpty{psubVars = Map.fromList [(x, PVar x) | (x, _, _) <- phi]}
    phi' <- forM phi $ \(x, ty@(RType v _ _), xs) -> do
      template <- mkPhiVar li (psubAddVar x (PVar v) declPsub) x ty
      pure (x, template, xs)

    let mkPhiCons penv getArg =
          genInvCons penv li (Map.fromList [(y, EVar (getArg ys)) | (y, _, ys) <- phi]) PropNone
    unless returnThen $ mkPhiCons thenEnv head
    unless returnElse $ mkPhiCons elseEnv (if returnThen then head else head . tail)
    when (returnThen && not returnElse) $ modifyEnv (localEnvAddPred (PNot cond))
    when (returnElse && not returnThen) $ modifyEnv (localEnvAddPred cond)
    pure (SIf phi' e sThen' sElse')
  SWhile phi e block -> do
    initEnv <- getEnv
    -- Define phi node variables
    let phiVars = [(x, ty) | (x, ty, _) <- phi]
    (li, _) <- mkInfPred (localEnvVarAssoc initEnv) (Left phiVars) InfPredLoop
    let declPsub = psubEmpty{psubVars = Map.fromList [(x, PVar x) | (x, _) <- phiVars]}
    phi' <- forM phi $ \(x, ty, args) -> do
      template <- mkPhiVar li declPsub x ty
      pure (x, template, args)

    entryEnv <- getEnv
    -- Generate constraints for initial values
    let phiInitVars = [(x, head args) | (x, _, args) <- phi]
    let initPsub = Map.fromList [(x, EVar xi) | (x, xi) <- phiInitVars]
    genInvCons initEnv li initPsub PropLoopInv

    -- Descend into the block
    let cond = exprToPred e
    _ <- consGenExpr e
    modifyEnv (localEnvAddPred cond)
    (block', _) <- consGenBlock block

    -- Generate constraints for the values at end of iteration
    bodyEnv <- getEnv
    let phiBodyVars = [(x, head (tail args)) | (x, _, args) <- phi]
    let bodyPsub = Map.fromList [(x, EVar xi) | (x, xi) <- phiBodyVars]
    genInvCons bodyEnv li bodyPsub PropLoopInv

    -- Now restore the outer scope with the path condition negated
    putEnv entryEnv
    modifyEnv (localEnvAddPred (PNot cond))
    pure (SWhile phi' e block')
  SAsn{} -> error "consGen: unexpected assignment; should be in SSA form"
  SCall [] "assert" [e] -> do
    skel <- consGenExpr e
    env <- getEnv
    emitCons env skel (mkVarEqExpr "v" TyBool (EConst (CBool True))) PropAssert
    modifyEnv (localEnvAddPred (exprToPred e))
    pure (SCall [] "assert" [e])
  SCall [] f [e] | f `elem` ["assume", "require"] -> do
    env <- getEnv
    let replaceOverflowCheck = \case
          ERel RelGte add@(EArith2 op (EVar x) _) (EVar y)
            | op `elem` [AAdd, AMul]
            , x == y -> (ERel RelLte add (EConst (CInt uint256Max)), False)
          _ -> (e, True)
        (e', shouldGenCons) = replaceOverflowCheck e
        p = exprToPred e'
    when shouldGenCons $ consGenExpr e' *> pure ()
    putEnv (localEnvAddPred p env)
    pure (SCall [] "assume" [e])
  SCall [(x, RType v ty _)] "$__array_push" [e, item] -> do
    _ <- consGenExpr e
    _ <- consGenExpr item
    let len = PField (exprToPred e) "length"
    let lenPlus1 = PArith2 AAdd len (PConst (CInt 1))
    let noOverflow = PRel RelLte lenPlus1 (PConst (CInt uint256Max))
    modifyEnv (localEnvAddPred noOverflow)
    let e' = PMapPut (PFieldUpd (exprToPred e) "length" lenPlus1) len (exprToPred item)
    let ty' = mkVarPred v (shapeSkel ty) (PRel RelEq (PVar v) e')
    modifyEnv (localEnvUpdateVar x ty')
    pure (SCall [(x, ty')] "$__array_push" [e])
  SCall [(x, RType v ty _)] "$__array_pop" [e] -> do
    _ <- consGenExpr e
    itemTy <- case ty of
      TyArray ity _ -> resolveSkel (shapeSkel ity)
      _ -> undefined
    let len = PField (exprToPred e) "length"
    let lenMinus1 = PArith2 ASub len (PConst (CInt 1))
    let noOverflow = PRel RelGt len (PConst (CInt 0))
    modifyEnv (localEnvAddPred noOverflow)
    let item = zeroValue itemTy
    let e' = PFieldUpd (PMapPut (exprToPred e) lenMinus1 (PConst item)) "length" lenMinus1
    let ty' = mkVarPred v (shapeSkel ty) (PRel RelEq (PVar v) e')
    modifyEnv (localEnvUpdateVar x ty')
    pure (SCall [(x, ty')] "$__array_pop" [e])
  SCall decls name args -> do
    -- Struct fields
    fldsM <- gets (Map.lookup name . delta_structs . stDelta)
    -- Fun decls
    funM <- gets (Map.lookup name . delta_funs . stDelta)
    decls' <-
      if | Just flds <- fldsM, [(x, _)] <- decls -> do
             -- Struct constructor
             fldTys <- forM (flds `zip` args) $ \((y, _), e) -> (y,) <$> consGenExpr e
             let ty = TyStruct name fldTys
             pure $ [(x, RType "v" ty (predicate PTrue))]
         | Just (fargs, frets, _) <- funM -> do
             -- Function call
             env <- getEnv
             (liArgs, liRes) <- gets ((`unsafeLookup` name) . stFunctionSig)
             -- Check arg types
             let psubArgs = psubEmpty{psubVars = Map.fromList [(x, exprToPred e) | (e, (x, _)) <- args `zip` fargs]}
             forM_ (args `zip` fargs) $ \(e, (x, RType v ty _)) -> do
               eSkel <- consGenExpr e
               let psubArgs' = psubAddVar x (PVar v) psubArgs
               emitCons env eSkel (RType v ty (LIVar liArgs psubArgs')) PropFunArg
             -- Check return types
             let psubRets = psubArgs <> psubEmpty{psubVars = Map.fromList [(rx, PVar x) | ((x, _), (rx, _)) <- decls `zip` frets]}
             pure [ (x, RType v ty (LIVar liRes (psubAddVar rx (PVar v) psubRets)))
                  | ((x, _), (rx, RType v ty _)) <- decls `zip` frets]
         | otherwise ->
           error "consGen: unknown struct/function call"
    forM_ decls' $ \(x, skel) -> do
      env <- getEnv
      modifyEnv (localEnvUpdateVar x skel)
      modify (\st -> st { stVarSkels = Map.insert x (env, skel) (stVarSkels st) })
    pure $ SCall decls' name args
  SFetch fs isDecl -> do
    -- All newly fetched variables should be in scope.
    let mkFetch (psub, fetchAcc) (x, RType _ ty _, l) = do
          -- For the constructor, we need to zero-initialize the first fetch.
          isInitLoc <- gets (Set.member l . stCtorFetch)
          template <- if isInitLoc
            then do
              modify (\c -> c { stCtorFetch = Set.delete l (stCtorFetch c) })
              ty' <- resolveSkel (shapeSkel ty)
              pure (exprSkel ty' (EConst (zeroValue ty')))
            else gets (fromJust . globalEnvLookupLoc l . stGlobalEnv)
          -- but don't create the constraints yet
          -- Collect the pending subs
          pure (psubAddLoc l (PVar x) psub, (x, template, l) : fetchAcc)
    (psub, fs') <- foldM mkFetch (mempty, []) fs
    -- Now we can create the templates by pushing the pending subs:
    fs'' <- forM (reverse fs') $ \(x, template, l) -> do
      -- Now we can create the local
      -- TODO: Solve.hornSolve can't handle the "proper" handling of pending subs here
      let psub' = psub -- {psubLocs = Map.insert l (EVar v) (psubLocs psub)}
      let template' = pushPendingSub psub' template
      env <- getEnv
      modifyEnv (localEnvUpdateVar x template')
      modify (\st -> st { stVarSkels = Map.insert x (env, template') (stVarSkels st)
                        , stGlobalEnv = globalEnvSetCheckout l x (stGlobalEnv st) })
      pure (x, template', l)
    pure (SFetch fs'' isDecl)
  SCommit cs -> do
    env <- getEnv
    let psub = mempty{psubLocs = Map.map exprToPred $ Map.fromList cs}
    -- Check that manually annotated contract invariants hold
    gEnv <- gets stGlobalEnv
    forM_ cs $ \(l, e) -> do
      skelE <- consGenExpr e -- TODO: do this in a separate loop
      case fromJust $ globalEnvLookupLoc l gEnv of
        skelL@(RType v _ (LIForm _)) ->
          emitCons
            env
            (exprSkel (rtypeSkel skelE) e)
            (pushPendingSub (psubAddLoc l (PVar v) psub) skelL) PropNone
        _ -> pure ()
    -- Check that the inferred contract invariant holds
    contractInv <- gets stContractInv
    isCtor <- gets ((== Just "<constructor>") . stCurFun)
    emitCons
      env
      (exprSkel TyBool (EConst (CBool True)))
      (RType "v" TyBool (LIVar contractInv psub))
      (PropContractInv isCtor)
    pure (SCommit cs)
  SAnnot a -> case a of
    ASubtype x (RType v t2 p) -> do
      s1 <- gets (rtypeSkel . fromJust . localEnvLookup x . stLocalEnv)
      env <- getEnv
      t2' <- resolveSkel (predicate <$> t2)
      emitCons env (exprSkel s1 (EVar x)) (RType v t2' (predicate p)) PropNone
      pure (SAnnot a)
    AAscribe{} -> pure (SAnnot a)
    AAssume p -> modifyEnv (localEnvAddPred p) >> pure (SAnnot a)
    AReachable -> error "consGenStmt: AReachable not implemented yet"
    ADefQual{} -> pure (SAnnot a)
    APhiReorder{} -> pure (SAnnot a)
  SReturn es -> do
    _ <- traverse consGenExpr es
    env <- getEnv
    modify (\st -> st{stReturnValues = (env, es) : stReturnValues st })
    pure (SReturn es)
  SHavoc -> pure SHavoc
  SAbort -> pure SAbort

-- | Generate constraints for the expression, returning the resulting type
-- skeleton.
consGenExpr :: Expr -> ConsGenM LIRType
consGenExpr = \case
  EConst c -> pure (constType c)
  EVar x -> exprSkel <$> gets (rtypeSkel . fromJust . localEnvLookup x . stLocalEnv) <*> pure (EVar x)
  e@(ERel _ e1 e2) -> consGenExpr e1 *> consGenExpr e2 *> pure (exprSkel TyBool e)
  e@(EBoolOp bop) -> do
    case bop of
      BAnd e1 e2 -> consGenExpr e1 *> consGenExpr e2 *> pure ()
      BOr e1 e2 -> consGenExpr e1 *> consGenExpr e2 *> pure ()
      BNot e1 -> consGenExpr e1 *> pure ()
    pure (exprSkel TyBool e)
  e@(EArith2 op e1 e2) -> do
    t1 <- consGenExpr e1
    t2 <- consGenExpr e2
    env <- getEnv
    let sz =
          if | TyInt m1 <- rtypeSkel t1, TyInt m2 <- rtypeSkel t2 -> skelIntMerge m1 m2
             | otherwise -> error $ "internal error: arithmetic arguments not integers: " <> show e
    let resBound = uintMax (fromMaybe 256 sz)
    let mkRtype v t f = RType v t $ predicate (f (PVar v))
    let overflowSkel =
          mkRtype "v" TyBool (\v -> PRel RelEq v (PRel RelLte (exprToPred e) (PConst (CInt resBound))))
    let skelTrue = constType (CBool True)
    case op of
      AAdd -> do
        emitCons env overflowSkel skelTrue PropSafeMath
        putEnv (localEnvAddPred (PRel RelLte (exprToPred e) (PConst (CInt resBound))) env)
      ASub -> do
        let e1Gte2 = mkRtype "v" TyBool (\v -> PRel RelEq v (PRel RelGte (exprToPred e1) (exprToPred e2))) in
          emitCons env e1Gte2 skelTrue PropSafeMath
        putEnv (localEnvAddPred (PRel RelGte (exprToPred e1) (exprToPred e2)) env)
      AMul -> do
        -- Check for overflow
        emitCons env overflowSkel skelTrue PropSafeMath
        putEnv (localEnvAddPred (PRel RelLte (exprToPred e) (PConst (CInt resBound))) env)
      ADiv -> do
        let gtZero = PRel RelGt (exprToPred e2) (PConst (CInt 0))
        -- emitCons env (mkRtype "v" TyBool (\v -> PRel RelEq v gtZero)) skelTrue PropSafeMath
        -- Since this is a runtime check, we can assume the dividend is not zero.
        modifyEnv (localEnvAddPred gtZero)
      _ -> pure ()
    pure (mkVarEqExpr "v" (TyInt Nothing) e)
  e@(EMapInd e1 i) -> do
    e1ty <- consGenExpr e1
    _ <- consGenExpr i
    case e1ty of
      RType v (TyMapping _ t2) _ -> do
        -- assert on each path that sum(..(e1[i])) <= sum(e1)
        delta <- gets stDelta
        let elemPaths = (if disable_fig10_ then Set.filter (== Agg.I) else id) $ Agg.splitPath delta t2
            sumProp path = PRel RelLte (elemOps (exprToPred e)) (aggOps (exprToPred e1))
              where
                elemOps = Agg.pathToPred path
                aggOps = Agg.pathToPred (Agg.M path)
            ps = Set.map sumProp elemPaths
        forM_ ps (modifyEnv . localEnvAddPred)
        pure (RType v t2 (predicate (PRel RelEq (PVar v) (exprToPred e))))
      RType _ (TyArray t _) _ ->
        boundsCheck e1 i >> pure (exprSkel t e)
      ty -> error (show ty)
  e@(EMapPut em i enew) -> do
    RType v xty _ <- consGenExpr em
    _ <- consGenExpr i
    _ <- consGenExpr enew
    delta <- gets stDelta
    case xty of
      t@(TyMapping _ tval) -> do
        let elemPaths = (if disable_fig10_ then Set.filter (== Agg.I) else id) $ Agg.splitPath delta tval
            sumProp path = PRel RelEq (aggOps (PVar v)) rhs
              where
                elemOps = Agg.pathToPred path
                aggOps = Agg.pathToPred (Agg.M path)
                poldM = aggOps (exprToPred em)
                pmi = elemOps (PMapInd (exprToPred em) (exprToPred i))
                pnew = elemOps (exprToPred enew)
                rhs = PArith2 AAdd (PArith2 ASub poldM pmi) pnew
            nnzProp = Set.fromList (mkNnz <$> (paths >>= (Agg.pathToNnz . Agg.M)))
              where
                paths = Set.toList (Agg.splitPath delta tval)
                mkNnz f = PUnintFn "nnzupd" [f (PVar v), f (exprToPred em), PMapInd (exprToPred em) (exprToPred i), exprToPred enew]
            ps = nnzProp <> Set.map sumProp elemPaths
            ref = foldl PAnd (PRel RelEq (PVar v) (exprToPred e)) ps
        -- MapPut can only occur in RHS of an assignment, so attach the property to the type
        pure (RType v t (predicate ref))
      t@(TyArray _ _) ->
        boundsCheck em i >> pure (mkVarEqExpr v t e)
      _ -> undefined
  e@(EField e1 f) -> do
    RType v ty _ <- consGenExpr e1
    case ty of
      TyArray _ _ | f == "length" -> pure $ mkVarEqExpr v (TyInt Nothing) e
      TyStruct name _ -> do
        flds <- gets ((`unsafeLookup` name) . delta_structs. stDelta)
        let RType vf bty _ = (Map.fromList flds) `unsafeLookup` f in
          pure (RType vf bty (LIForm (PRel RelEq (PVar vf) (exprToPred e))))
      _ -> undefined
  e@(EFieldUpd e1 f ef) -> do
    RType v tyS _ <- consGenExpr e1
    case tyS of
      TyStruct name _ -> do
        _ <- consGenExpr ef
        {-
        flds <- gets ((`unsafeLookup` name) . delta_structs. stDelta)
        let RType _ tf _ = (Map.fromList flds) `unsafeLookup` f
            flds' = [ (x, if x /= f then exprSkel t (EField e1 x) else exprSkel tf ef)
                    | (x, RType _ t _) <- flds] in
        -}
        let flds' = [] in
          pure (mkVarEqExpr v (TyStruct name flds') e)
      TyArray _ _ | f == "length" -> pure (mkVarEqExpr v tyS e)
      _ -> error $ "consGenExpr: field update on invalid expression: " <> show e
  EUnintFn{} -> undefined -- Cannot occur in the program
  EHavoc ty -> pure (RType "v" (shapeSkel ty) (predicate PTrue))
  ECast e ty -> do
    ety <- consGenExpr e
    let eskel = rtypeSkel ety
    if | TyInt n <- eskel, TyInt m <- ty, n <= m ->
         -- Cast smaller int to larger int --> retain same value
         pure (exprSkel (TyInt m) e)
       | TyAddress <- ty, TyInt _ <- eskel -> pure (exprSkel TyAddress e)
       | otherwise -> pure $ mkVarPred "v" (shapeSkel ty) PTrue
  where
    -- This is a dynamic check, so add it to the path condition.
    boundsCheck (exprToPred -> a) (exprToPred -> i) = do
      let bounds = PAnd (PRel RelLte (PConst (CInt 0)) i) (PRel RelLt i (PField a "length"))
      modifyEnv (localEnvAddPred bounds)
      -- env <- getEnv
      -- tell [JSubtype env ity (RType "v" (TyInt Nothing) (predicate bounds)) PropNone]
      pure ()
    disable_fig10_ = False

-- * Helper functions

mkVarPred :: Text -> LISkel -> Pred -> LIRType
mkVarPred v t p = RType v t (predicate p)

mkVarEqExpr :: Text -> LISkel -> Expr -> LIRType
mkVarEqExpr v t e = mkVarPred v t (PRel RelEq (PVar v) (exprToPred e))

-- | Generate constraint
emitCons :: LiLocalEnv -> LIRType -> LIRType -> PropTag -> ConsGenM ()
emitCons env t1 t2 prop = do
  srcTagFun <- gets stCurFun
  srcTagLoc <- gets stCurSrcLoc
  tell [JSubtype env t1 t2 (((,srcTagLoc) <$> srcTagFun), prop)]
