{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.SolToAst where

import Data.List (partition)
import LiquidSol.SrcLoc (SrcLoc(..))
import qualified LiquidSol.Solidity.Syntax as Sol
import qualified LiquidSol.Syntax as Ast
import Data.DList (DList)
import qualified Data.DList as DList
import qualified Data.HashMap.Strict as HashMap
import Data.Text (Text)
import qualified Data.Text as Text
import LiquidSol.Solidity.PrettyPrint (prettyExpr, prettyStmt)
import LiquidSol.Util.Unsafe
import qualified Data.List.NonEmpty as NE
import LiquidSol.Solidity.Inliner (functionHasBytes, functionHasAsm)
import LiquidSol.Solidity.ContextMonad (getFunctionSig)
import LiquidSol.Solidity.Asm as Asm
import LiquidSol.Solidity.Types (bytesTypes, uintTypes)
import qualified Data.Set as Set
import Data.HashMap.Strict (HashMap)
import Data.Maybe (catMaybes)
import GHC.Stack (HasCallStack)

flattenBlock :: Sol.SourceCtx -> [Sol.StmtRef] -> [Sol.StmtRef]
flattenBlock ctx stmts = flip concatMap stmts $ \r -> case Sol.lookupRef r ctx of
  Sol.SolStmtBlock refs -> flattenBlock ctx refs
  _ -> [r]

convertContract :: Sol.SourceCtx -> Sol.SolContract -> Ast.Contract ()
convertContract ctx Sol.SolContract{Sol.contract_name=name, Sol.contract_body=body} =
  -- collect annotations in the contract body
  let (bounds, body') = unzip . catMaybes $ [mkCbody cbodyRef | cbodyRef <- body]
      isInBody (i, _) = all (\(b, e) -> i < b || i > e) bounds
      (bodyAnnots, funAnnots) = partition isInBody (Sol.srcCtx_annots ctx)
      -- this has two purposes:
      -- 1) compute the bounds of the cbody
      -- 2) translate the cbody to the IR
      mkCbody ref =
        let loc = (Sol.srcCtx_locs ctx) `hmUnsafeLookup` (Sol.asNodeRef ref)
            begin = Sol.srcLoc_offs loc
            end = begin + Sol.srcLoc_len loc
            -- Find which annotations are contained within this cbody.
            cbodyAnnots = filter (\(i, _) -> begin < i && i < end) funAnnots
            -- Here, we actually convert the cbody.
            cbody' = convertCbody ctx (Sol.lookupRef ref ctx{Sol.srcCtx_annots = cbodyAnnots})
        in ((begin, end),) <$> cbody'
  in Ast.Contract name (body' <> [Ast.DAnnot a | (_, a) <- bodyAnnots])

convertVis :: Sol.SolVis -> Ast.Visibility
convertVis = \case
  Sol.VisPrivate -> Ast.VisInt
  Sol.VisInternal -> Ast.VisInt
  Sol.VisPublic -> Ast.VisExt
  Sol.VisExternal -> Ast.VisExt

convertMutability :: Sol.SolMut -> Ast.Mutability
convertMutability = \case
  Sol.MutPayable -> Ast.MutStateful
  Sol.MutNone -> Ast.MutStateful
  Sol.MutView -> Ast.MutReadonly
  Sol.MutPure -> Ast.MutStateless

convertCbody :: Sol.SourceCtx -> Sol.SolCbody -> Maybe (Ast.Decl ())
convertCbody ctx = \case
  Sol.CStateVar (flip Sol.lookupRef ctx -> decl) ->
    let ty = convertType ctx (Sol.varDecl_type decl)
        expr = fmap (snd . convertExpr ctx) (Sol.varDecl_value decl) in
      Just $ Ast.DVar (Sol.varDecl_name decl) ty expr (Ast.Loc 0)
  Sol.CFun{ Sol.cfun_name=name, Sol.cfun_args=args, Sol.cfun_rets=rets
          , Sol.cfun_body=Just body, Sol.cfun_isCtor=isCtor, Sol.cfun_vis=vis
          , Sol.cfun_mut=mut } ->
    let args' = convertParam  <$> args
        rets' = [(if Text.null x then "__anon_ret" <> Text.pack (show i) else x, ty)
                | (i, (x, ty)) <- [(0 :: Int)..] `zip` (convertParam <$> rets)]
        body' = DList.toList (convertStmt ctx body)
        vis' = convertVis vis
        hasAsm = functionHasAsm body ctx
        bodyLoc = Sol.sourceCtxGetLoc body ctx
        havocBody = (bodyLoc,) <$>
          Ast.SHavoc : [Ast.SAsn (Ast.LvVar x) (Ast.EHavoc (Ast.rtypeSkel ty))
                       | (x, ty) <- rets']
    in Just $
      if isCtor
      then Ast.DCtor{ Ast.dctor_args=args', Ast.dctor_body=body', Ast.dctor_loc=bodyLoc}
      else Ast.DFun{ Ast.dfun_name=name, Ast.dfun_args=args', Ast.dfun_res=rets'
                   , Ast.dfun_body=if hasAsm then havocBody else body',  Ast.dfun_vis=vis'
                   , Ast.dfun_loc=bodyLoc, Ast.dfun_mut=convertMutability mut }
  Sol.CStruct name fields -> Just $
    Ast.DStruct name [(x, convertType ctx ty)
                     | vdRef <- fields
                     , let Sol.SolVarDecl{Sol.varDecl_name=x, Sol.varDecl_type=ty} = Sol.lookupRef vdRef ctx]
  Sol.CEvent -> Nothing
  cb -> error $ show cb <> " currently not supported in contract body"
  where
    convertParam :: Sol.VarDeclRef -> (Text, Ast.UType)
    convertParam (flip Sol.lookupRef ctx ->
                  Sol.SolVarDecl{Sol.varDecl_name=name, Sol.varDecl_type=ty}) =
      (name, convertType ctx ty)

mkFunCall :: Sol.SourceCtx -> [(Text, Ast.UType)] -> Text -> [Sol.TypedRef Sol.SolExpr] -> DList (Ast.Stmt ())
mkFunCall ctx decls fname argrefs =
  let (stmts, args') = unzip $ convertExpr ctx <$> argrefs in
    mconcat stmts <> DList.singleton (Ast.SCall decls fname args')

convertStmtExpr :: Sol.SourceCtx -> Sol.ExprRef -> DList (Ast.Stmt())
convertStmtExpr ctx eref = case Sol.lookupRef eref ctx of
  Sol.SolExprAssign{} -> fst (convertExpr ctx eref)
  Sol.SolExprFunCall fnref argrefs
    -- For require, ignore the string argument.
    | Sol.SolExprIdent "require" _ <- Sol.lookupRef fnref ctx
    , (re:_) <- argrefs ->
      mkFunCall ctx [] "require" [re]
    -- Convert revert(), selfdestruct(_) to assume false
    | Sol.SolExprIdent fname  _ <- Sol.lookupRef fnref ctx
    , fname `elem` ["revert", "selfdestruct"] ->
      pure Ast.SAbort
    -- Built in function call
    {-
    | Sol.SolExprIdent builtin  _ <- Sol.lookupRef fnref ctx
    , Just _ <- HashMap.lookup builtin builtinFuns ->
      -- Nothing to do, so just generate effectful statements.
      let (stmts, _) = unzip (convertExpr ctx <$> argrefs) in
        mconcat stmts
    -}
    -- Ordinary function calls
    | Sol.SolExprIdent fname _ <- Sol.lookupRef fnref ctx ->
      mkFunCall ctx [] fname argrefs
    -- Array push
    | Sol.SolExprMember e1 "push" _ <- Sol.lookupRef fnref ctx
    , Sol.SolExprIdent _ vdRef <- Sol.lookupRef e1 ctx
    , Just (Sol.varDecl_type -> ty@Sol.SolTyArr{}) <- Sol.tryLookupRef vdRef ctx
    , [arg] <- argrefs ->
      let (stmts, e1') = convertExpr ctx e1
          (stmtsArg, arg') = convertExpr ctx arg
          ty' = convertType ctx ty
          tmpVar = "expr#" <> Text.pack (show (Sol.asNodeRef eref))
          call = Ast.SCall [(tmpVar, ty')] "$__array_push" [e1', arg']
          asn = Ast.SAsn (mkLvalue e1') (Ast.EVar tmpVar)
      in
        stmts <> stmtsArg <> DList.fromList [call, asn]
    | Sol.SolExprMember e1 "pop" _ <- Sol.lookupRef fnref ctx
    , Sol.SolExprIdent _ vdRef <- Sol.lookupRef e1 ctx
    , Just (Sol.varDecl_type -> ty@Sol.SolTyArr{}) <- Sol.tryLookupRef vdRef ctx
    , [] <- argrefs ->
      let (stmts, e1') = convertExpr ctx e1
          ty' = convertType ctx ty
          tmpVar = "expr#" <> Text.pack (show (Sol.asNodeRef eref))
          call = Ast.SCall [(tmpVar, ty')] "$__array_pop" [e1']
          asn = Ast.SAsn (mkLvalue e1') (Ast.EVar tmpVar)
      in
        stmts <> DList.fromList [call, asn]
    | Just (_, _, mut) <- getFunctionSig fnref ctx, Sol.MutView <= mut ->
      DList.empty
    | otherwise -> DList.singleton Ast.SHavoc
  Sol.SolExprUnaryOp "++" lvRef -> mkInc Ast.AAdd lvRef
  Sol.SolExprUnaryOp "--" lvRef -> mkInc Ast.ASub lvRef
  Sol.SolExprUnaryOp "delete" lvRef ->
    case HashMap.lookup lvRef (Sol.srcCtx_exprTypes ctx) of
      Just solTy ->
        let (stmts, lv) = convertExpr ctx lvRef
            ty = Ast.rtypeSkel (convertType ctx solTy)
            mkZero = case solTy of
              Sol.SolTyUser tr _
                | Just (Sol.CStruct n fldRefs) <- Sol.tryLookupRef tr ctx
                , flds <- flip Sol.lookupRef ctx <$> fldRefs ->
                  Ast.zeroValue (Ast.TyStruct n
                                 [(Sol.varDecl_name f, convertType ctx (Sol.varDecl_type f))
                                 | f <- flds])
              _ -> Ast.zeroValue ty
        in
          stmts <> DList.singleton (Ast.SAsn (mkLvalue lv) (Ast.EConst mkZero))
      Nothing -> error $ "could not parse type of: " <> show (prettyExpr ctx lvRef)
  Sol.SolExprIdent "this" _ -> DList.empty
  s -> error $ show s <> " is an unsupported ExpressionStatement"
  where
    mkInc op lvRef =
      let (stmts, lv) = convertExpr ctx lvRef
          rhs = Ast.EArith2 op lv (Ast.EConst (Ast.CInt 1)) in
        stmts <> DList.singleton (Ast.SAsn (mkLvalue lv) rhs)

-- | Returns true if the given callee belongs to a .call chain
isCall :: Sol.SourceCtx -> Sol.ExprRef -> Bool
isCall ctx eref = case Sol.lookupRef eref ctx of
  Sol.SolExprFunCall (flip Sol.lookupRef ctx -> lhs) _
    -- .value()
    | Sol.SolExprMember e1ref fname _ <- lhs, fname `elem` ["value", "gas"] -> isCall ctx e1ref
  Sol.SolExprMember _ "call" _ -> True
  Sol.SolExprMember _ "send" _ -> True
  _ -> False

convertStmt :: Sol.SourceCtx -> Sol.StmtRef -> DList (SrcLoc, Ast.Stmt ())
convertStmt ctx curRef = case Sol.lookupRef curRef ctx of
  Sol.SolStmtBlock bodyRefs ->
    -- TODO: refactor this into Toolchain.prepareSol
    let Sol.SrcLoc blkOffs blkLen = Sol.sourceCtxGetLoc curRef ctx
        blkFold (stmts, curLoc, ctx') nextRef =
          -- insert annotations between the previous statement and the current one
          let loc = Sol.sourceCtxGetLoc nextRef ctx'
              i = Sol.srcLoc_offs loc
              len = Sol.srcLoc_len loc
              (annotsHere, annotsThere) =
                partition (\(ia, _) -> curLoc < ia && ia < i) (Sol.srcCtx_annots ctx)
              annots = DList.fromList $ [(loc, Ast.SAnnot a) | (_, a) <- annotsHere]
              nextStmts = convertStmt ctx nextRef
          in
            (stmts <> annots <> nextStmts, i + len, ctx'{Sol.srcCtx_annots = annotsThere})
        (finalStmts, finalOffs, finalCtx) = foldl blkFold (mempty, blkOffs, ctx) bodyRefs in
      -- insert annotations between the last statement and the end of the block
      finalStmts <> attachLoc (DList.fromList [ Ast.SAnnot a | (ia, a) <- Sol.srcCtx_annots finalCtx
                                              , finalOffs < ia && ia < blkOffs + blkLen ])
    -- foldMap (convertStmt ctx) (flattenBlock ctx [curRef])
  Sol.SolStmtExpr eref -> attachLoc $ convertStmtExpr ctx eref
  -- Assignment
  Sol.SolStmtVarDecl (NE.toList -> vdRefs) exprMaybe ->
    let vds = flip Sol.lookupRef ctx <$> vdRefs
        dpairs = [(Sol.varDecl_name vd, convertType ctx (Sol.varDecl_type vd)) | vd <- vds]
        mkMutHavoc mut = if mut < Sol.MutView then DList.singleton Ast.SHavoc else DList.empty
    in
      attachLoc $ case exprMaybe of
        Just (flip Sol.lookupRef ctx -> Sol.SolExprFunCall fref argrefs)
          | Sol.SolExprIdent fname _ <- Sol.lookupRef fref ctx
          , Just (_, _, mut) <- getFunctionSig fref ctx ->
            mkMutHavoc mut <> mkFunCall ctx dpairs fname argrefs
          | Sol.SolExprMember _ _ mr <- Sol.lookupRef fref ctx ->
            let (stmts', _) = unzip (convertExpr ctx <$> argrefs)
                declStmts = [Ast.SDecl x t (Just (Ast.EHavoc (Ast.rtypeSkel t))) | (x, t) <- dpairs]
                havocStmt = case mr of
                  Just r
                    | Just Sol.CFun{Sol.cfun_mut=mut} <- Sol.tryLookupRef r ctx -> mkMutHavoc mut
                  _ -> DList.empty
            in
              mconcat stmts' <>
              havocStmt <>
              DList.fromList declStmts
          | isCall ctx fref ->
            let (stmts', _) = unzip (convertExpr ctx <$> argrefs)
                declStmts = [Ast.SDecl x t (Just (Ast.EHavoc (Ast.rtypeSkel t))) | (x, t) <- dpairs] in
              mconcat stmts' <> DList.singleton Ast.SHavoc <> DList.fromList declStmts
        Just e | [(name, ty)] <- dpairs ->
          let (stmts, e') = convertExpr ctx e in
              DList.snoc stmts (Ast.SDecl name ty (Just e'))
        Nothing -> DList.fromList [Ast.SDecl name ty Nothing | (name, ty) <- dpairs]
        _ -> error $ "convertExpr: cannot handle assignment: " <> show (prettyStmt ctx curRef)
  Sol.SolStmtIf e bthen belse ->
    let (se, e') = convertExpr ctx e
        bthen' = convertStmt ctx bthen
        belse' = maybe [] (\b -> DList.toList $ convertStmt ctx b) belse
    in
      attachLoc $ se <> DList.singleton (Ast.SIf [] e' (DList.toList bthen') belse')
  Sol.SolStmtWhile e body ->
    let (se, e') = convertExpr ctx e
        body' = convertStmt ctx body in
      attachLoc $ se <> DList.singleton (Ast.SWhile [] e' (DList.toList body'))
  Sol.SolStmtFor{} -> error $ "convertStmt: unexpected for loop, expand it first"
  Sol.SolStmtEmit{} ->
    -- Treat as no-op
    DList.empty
  Sol.SolStmtReturn [e]
    -- TODO: this won't be needed with ANF transforms.
    | Sol.SolExprFunCall e1 eargs <- Sol.lookupRef e ctx
    , Just (Sol.SolTyTuple ts) <- HashMap.lookup e (Sol.srcCtx_exprTypes ctx) ->
      let havocs = [Ast.EHavoc (Ast.rtypeSkel (convertType ctx t)) | t <- ts]
          (stmts1, _) = convertExpr ctx e1
          (stmtsArgs, _) = unzip (convertExpr ctx <$> eargs) in
        attachLoc $ stmts1 <> mconcat stmtsArgs <> pure (Ast.SReturn havocs)
  Sol.SolStmtReturn es ->
    let (se, es') = unzip $ (\e -> convertExpr ctx e) <$> es in
      attachLoc $ mconcat se <> DList.singleton (Ast.SReturn es')
  {-
  Sol.SolStmtAsm code ->
    -- TODO: generate correct havoc type instead of assuming everything is an integer
    let assigns = Set.difference (Asm.findAssigns code) (Asm.findLocals code)
        havocs = [Ast.SAsn (Ast.LvVar x) (Ast.EHavoc (Ast.TyInt Nothing)) | x <- Set.toList assigns] in
      DList.fromList havocs
  -}
  Sol.SolStmtThrow -> attachLoc $ DList.singleton $ Ast.SAbort
  s -> error $ show s <> " currently not a supported statement"
  where
    attachLoc :: HasCallStack => DList (Ast.Stmt p) -> DList (SrcLoc, Ast.Stmt p)
    attachLoc ss =
      let loc = Sol.sourceCtxGetLoc curRef ctx in
        (loc,) <$> ss

convertType :: HasCallStack => Sol.SourceCtx -> Sol.SolType -> Ast.RType ()
convertType ctx = \case
  Sol.SolTyElem t ->
      case t of
        "address" -> template Ast.TyAddress
        "address payable" -> template Ast.TyAddress
        "bool" -> template Ast.TyBool
        _ | t `elem` ["int", "int256", "uint"] -> template (Ast.TyInt (Just 256))
        _ | Just n <- HashMap.lookup t uintTypes -> template (Ast.TyInt (Just n))
        "byte" -> template (Ast.TyArray Ast.TyByte (Just 1))
        "string" -> template (Ast.TyArray Ast.TyByte Nothing)
        "bytes" -> template (Ast.TyArray Ast.TyByte Nothing)
        b | Just i <- HashMap.lookup b bytesTypes -> template (Ast.TyArray Ast.TyByte (Just i))
        _ -> error $ "unknown SolTyElem: " <> show t
  Sol.SolTyUser declRef sname
    | Just _ <- Sol.tryLookupRef @Sol.SolContract declRef ctx ->
        template Ast.TyAddress
    | otherwise ->
        template $ Ast.TyStruct sname []
  Sol.SolTyArr t l -> template $ Ast.TyArray (Ast.rtypeSkel (convertType ctx t)) l
  Sol.SolTyMapping t1 t2 -> template $
    Ast.TyMapping (Ast.rtypeSkel (convertType ctx t1)) (Ast.rtypeSkel (convertType ctx t2))
  t -> error $ "convertType: unsupported type: " <> show t
  where
    template skel = Ast.RType "v" skel ()

builtinFuns :: HashMap Text Ast.USkel
builtinFuns = HashMap.fromList
  [ ("keccak256", Ast.TyArray Ast.TyByte (Just 32))
  , ("ripemd160", Ast.TyArray Ast.TyByte (Just 20))
  , ("blockhash", Ast.TyArray Ast.TyByte (Just 32))
  , ("ecrecover", Ast.TyAddress)
  , ("sha256", Ast.TyArray Ast.TyByte (Just 32))
  , ("sha3", Ast.TyArray Ast.TyByte (Just 32))
  ]

convertExpr :: HasCallStack => Sol.SourceCtx -> Sol.ExprRef -> (DList (Ast.Stmt ()), Ast.Expr)
convertExpr ctx eref = case Sol.lookupRef eref ctx of
  Sol.SolExprAssign op e1 e2 _ ->
    let (s1, e1') = convertExpr ctx e1
        (s2, e2') = convertExpr ctx e2
        rhs = case op of
          "=" -> e2'
          "+=" -> Ast.EArith2 Ast.AAdd e1' e2'
          "-=" -> Ast.EArith2 Ast.ASub e1' e2'
          "*=" -> Ast.EArith2 Ast.AMul e1' e2'
          "/=" -> Ast.EArith2 Ast.ADiv e1' e2'
          _ -> error $ "unsupported assignment operator: " <> Text.unpack op
        stmt = Ast.SAsn (mkLvalue e1') rhs in
      (s1 <> s2 <> DList.singleton stmt, e1')
  Sol.SolExprLit lit ->
    let
      c = Ast.EConst $ case lit of
        Sol.SolLitInt i -> Ast.CInt i
        Sol.SolLitAddr x -> Ast.CInt x
        Sol.SolLitBool b -> Ast.CBool b
        Sol.SolLitString s -> Ast.CString (Text.pack s)
    in
      (mempty, c)
  Sol.SolExprUnaryOp "-" e1ref
    | (stmts, Ast.EConst (Ast.CInt i)) <- convertExpr ctx e1ref ->
      (stmts, Ast.EConst (Ast.CInt (-i)))
  Sol.SolExprUnaryOp "!" e1ref ->
    let (stmts, e') =  convertExpr ctx e1ref in
      (stmts, Ast.EBoolOp (Ast.BNot e'))
  Sol.SolExprBinaryOp op e1 e2 ty ->
    let (s1, e1') = convertExpr ctx e1
        (s2, e2') = convertExpr ctx e2
        mkBop f b1 b2 = Ast.EBoolOp (f b1 b2)
        mkHavoc _ _ = Ast.EHavoc (Ast.rtypeSkel (convertType ctx ty))
        op' = case op of
          "+" -> Ast.EArith2 Ast.AAdd
          "-" -> Ast.EArith2 Ast.ASub
          "*" -> Ast.EArith2 Ast.AMul
          "/" -> Ast.EArith2 Ast.ADiv
          "%" -> Ast.EArith2 Ast.AMod
          ">" -> Ast.ERel Ast.RelGt
          "<" -> Ast.ERel Ast.RelLt
          ">=" -> Ast.ERel Ast.RelGte
          "<=" -> Ast.ERel Ast.RelLte
          "==" -> Ast.ERel Ast.RelEq
          "!=" -> Ast.ERel Ast.RelNeq
          "||" -> mkBop Ast.BOr
          "&&" -> mkBop Ast.BAnd
          _ | op `elem` ["&", "^", "|"] -> mkHavoc
          _ -> error $ "unsupported binary op: " <> show op
    in (s1 <> s2, if op == "**" then Ast.EHavoc (Ast.TyInt (Just 256)) else op' e1' e2')
  Sol.SolExprIdent "now" _ -> (mempty, Ast.EVar "$__block_timestamp")
  Sol.SolExprIdent x _ -> (mempty, Ast.EVar x)
  Sol.SolExprIndex e1 e2 ->
    let (stmts1, e1') = convertExpr ctx e1
        (stmts2, e2') = convertExpr ctx e2 in
      (stmts1 <> stmts2, Ast.EMapInd e1' e2')
  Sol.SolExprMember e1 member _ ->
    case Sol.lookupRef e1 ctx of
      Sol.SolExprIdent "msg" _ -> (mempty, Ast.EVar ("$__msg_" <> member))
      Sol.SolExprIdent "tx" _ | member == "origin" -> (mempty, Ast.EVar ("$__tx_" <> member))
      Sol.SolExprIdent "this" _ | member == "balance" -> (mempty, Ast.EHavoc (Ast.TyInt (Just 256)))
      Sol.SolExprIdent "block" _ -> (mempty, Ast.EVar ("$__block_" <> member))
      _ | Just (Sol.SolTyElem ty) <- HashMap.lookup e1 (Sol.srcCtx_exprTypes ctx)
        , ty `elem` ["address", "address payable"] ->
          let (stmts, _) = convertExpr   ctx e1 in
            (stmts, Ast.EHavoc (Ast.TyInt (Just 160)))
      _ -> let (stmts, e') = convertExpr ctx e1 in
        (stmts, Ast.EField e' member)
  Sol.SolExprTuple [e1] -> convertExpr ctx e1
  Sol.SolExprTypeConvert ty e1
    | Sol.SolTyElem tname <- ty
    , tname `elem` ["address", "uint"] <> HashMap.keys uintTypes ->
      let (stmts, e1') = convertExpr ctx e1 in
        (stmts, Ast.ECast e1' (Ast.rtypeSkel (convertType ctx ty)))
    | otherwise ->
        let (stmts, _) = convertExpr ctx e1 in
          (stmts, Ast.EHavoc (Ast.rtypeSkel (convertType ctx ty)))
  Sol.SolExprFunCall e1 args
    | Sol.SolExprNew (Sol.SolTyUser r _) <- Sol.lookupRef e1 ctx
    , Just Sol.SolContract{} <- Sol.tryLookupRef r ctx ->
      -- convert new Contract() to havoc address
      let (stmts, _) = unzip (convertExpr ctx <$> args) in
        (mconcat stmts <> DList.singleton Ast.SHavoc, Ast.EHavoc Ast.TyAddress)
    | Sol.SolExprNew (Sol.SolTyElem t) <- Sol.lookupRef e1 ctx
    , t `elem` ["bytes", "string"] ->
      -- havoc
      let (stmts, _) = unzip (convertExpr ctx <$> args)
          ty = Ast.rtypeSkel (convertType ctx (Sol.SolTyElem t)) in
        (mconcat stmts,  Ast.EConst (Ast.zeroValue ty))
    | Sol.SolExprNew (Sol.SolTyArr ety msz) <- Sol.lookupRef e1 ctx ->
      -- havoc
      let (stmts, _) = unzip (convertExpr ctx <$> args)
          ty = Ast.rtypeSkel (convertType ctx ety) in
        (mconcat stmts,  Ast.EConst (Ast.zeroValue (Ast.TyArray ty msz)))
    | Sol.SolExprIdent builtin _ <- Sol.lookupRef e1 ctx
    , Just ty <- HashMap.lookup builtin builtinFuns ->
      -- These builtin functions are pure, so do not generate a statement havoc
      let (stmts, _) = unzip (convertExpr ctx <$> args) in
        (mconcat stmts, Ast.EHavoc ty)
    | Just (_, retTys, mut) <- getFunctionSig e1 ctx ->
      let needsHavoc = mut < Sol.MutView
          shavoc = if needsHavoc then DList.singleton Ast.SHavoc else DList.empty in
      case retTys of
        [t] | Sol.SolExprIdent name _ <- Sol.lookupRef e1 ctx ->
          let declVar = Text.pack ("$__call_" <> show (Sol.asNodeRef e1))
              stmts = mkFunCall ctx [(declVar, convertType ctx t)] name args
              eret = Ast.EVar declVar in
          (stmts <> shavoc, eret)
        [t] -> (shavoc, Ast.EHavoc (Ast.rtypeSkel (convertType ctx t)))
        _ -> error $ "multi-return fun call used outside of statement: " <> show (prettyExpr ctx e1)
    | isCall ctx e1 ->
      -- this is in an expression position so assume it is a boolean
      let (stmts, _) = unzip (convertExpr ctx <$> args) in
        (mconcat stmts <> DList.singleton Ast.SHavoc, Ast.EHavoc Ast.TyBool)
    | Sol.SolExprMember e1ref _ _ <- Sol.lookupRef e1 ctx
    , Sol.SolExprIdent "abi" _<- Sol.lookupRef e1ref ctx ->
      let (stmts, _) = unzip (convertExpr ctx <$> args) in
        (mconcat stmts <> DList.singleton Ast.SHavoc, Ast.EHavoc (Ast.TyArray Ast.TyByte Nothing))
    | Sol.SolExprMember e1ref "blockhash" _ <- Sol.lookupRef e1 ctx
    , Sol.SolExprIdent "block" _<- Sol.lookupRef e1ref ctx ->
      let (stmts, _) = unzip (convertExpr ctx <$> args) in
        (mconcat stmts <> DList.singleton Ast.SHavoc, Ast.EHavoc (Ast.TyArray Ast.TyByte (Just 32)))
    | otherwise ->
      let node = Sol.srcCtx_nodes ctx `hmUnsafeLookup` (Sol.asNodeRef eref)
          tyStr = (Sol.node_attributes node) `hmUnsafeLookup` "type" in
      error $ "Failed to havoc function call, unknown type " <> show tyStr <> ": " <> show (prettyExpr ctx eref)
        <> show tyStr
  Sol.SolExprStructCons r args ->
    let name = case Sol.lookupRef r ctx of
          Sol.CStruct n _ -> n
          _ -> error "convertExpr: SolExprStructCons does not point to a struct declaration"
        (stmts, args') = unzip (convertExpr ctx <$> args)
        freshX = Text.pack ("$__struct_" <> show (Sol.asNodeRef eref))
        structTy = Ast.RType "v" (Ast.TyStruct name []) () in
      (mconcat stmts <> pure (Ast.SCall [(freshX, structTy)] name args'), Ast.EVar freshX)
  Sol.SolExprConditional e1 e2 e3
    | Just ty <- HashMap.lookup eref (Sol.srcCtx_exprTypes ctx) ->
      let (stmts1, e1') = convertExpr ctx e1
          (stmts2, e2') = convertExpr ctx e2
          (stmts3, e3') = convertExpr ctx e3
          e2loc = Sol.sourceCtxGetLoc e2 ctx
          e3loc = Sol.sourceCtxGetLoc e3 ctx
          x = Text.pack ("$__cond_" <> show (Sol.asNodeRef eref))
          stmts = DList.fromList
            [ Ast.SDecl x (convertType ctx ty) Nothing
            , Ast.SIf [] e1' [(e2loc, Ast.SAsn (Ast.LvVar x) e2')] [(e3loc, Ast.SAsn (Ast.LvVar x) e3')]]
      in
        (stmts1 <> stmts2 <> stmts3 <> stmts, Ast.EVar x)
    | otherwise -> error $ "unknown type of conditional: " <> show (prettyExpr ctx eref)
  _ -> error $ "unsupported expression: " <> show (prettyExpr ctx eref)

-- | Forcibly convert expression to lvalue
mkLvalue :: Ast.Expr -> Ast.LValue
mkLvalue = \case
  Ast.EVar x -> Ast.LvVar x
  Ast.EMapInd e1 e2 -> Ast.LvInd (mkLvalue e1) e2
  Ast.EField e f -> Ast.LvFld (mkLvalue e) f
  e -> error $ "unsupported (possible) lvalue: " <> show e
