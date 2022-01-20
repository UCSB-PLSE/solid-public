{-# LANGUAGE OverloadedStrings, FlexibleContexts, ScopedTypeVariables #-}

module LiquidSol.Typecheck where

import Control.Monad.Extra (whenM, fromMaybeM)
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Maybe (listToMaybe)
import Data.Foldable (forM_, traverse_)
import Data.Text (Text)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Functor.Identity

import LiquidSol.Syntax
import LiquidSol.LiquidTypes (Delta(..), deltaEmpty, deltaResolveSkel, solidityGlobalVars)
import qualified Data.Text.Encoding
import qualified Data.ByteString as ByteString
-- import LiquidSol.Util.Unsafe (unsafeLookup)

type ErrorTrace = [Either (Stmt ()) Expr]

-- | Variable typing context: maps variable names to types
data VarCtx = VarCtx { ctxVars :: Map Text USkel
                     , ctxLocs :: Map Loc USkel
                     , ctxDelta :: Delta ()
                     , ctxErrLoc :: ErrorTrace }
  deriving (Show, Eq, Ord)

varCtxEmpty :: VarCtx
varCtxEmpty = VarCtx{ ctxVars=Map.fromList [(x, rtypeSkel t) | (x, t) <- solidityGlobalVars]
                    , ctxDelta = deltaEmpty, ctxLocs = Map.empty
                    , ctxErrLoc = [] }

varCtxModify :: (Map Text USkel -> Map Text USkel) -> VarCtx -> VarCtx
varCtxModify f c@VarCtx{ctxVars=gamma} = c{ctxVars=f gamma}

varCtxLookup :: Text -> VarCtx -> Maybe USkel
varCtxLookup v VarCtx{ctxVars=gamma} = Map.lookup v gamma

data TypeError
  = TyErrUnknownVar Text
  | TyErrUnknownField USkel Text
  | TyErrMismatch USkel USkel
  | TyErrExpBase USkel
  | TyErrExpMapping USkel USkel (Maybe USkel)
  | TyErrExpArray USkel (Maybe USkel)
  | TyErrArgCount Int Int
  | TyErrRedef Text
  | TyErrInvalidDef Text USkel
  | TyErrInvalidType USkel
  | TyErrInvalidInd USkel
  | TyErrQualInBody
  deriving (Show, Eq, Ord)

-- -- | Storage context: maps references to storage locations
-- newtype StoContext = StoContext (Map Int Loc)

newtype TyCheckT m a = TyCheckM
  { unTyCheckM :: StateT VarCtx (ExceptT (TypeError, ErrorTrace) m) a }
  deriving (Functor, Applicative, Monad,
            MonadState VarCtx, MonadError (TypeError, ErrorTrace))

typeError :: Monad m => TypeError -> TyCheckT m a
typeError err = gets ctxErrLoc >>= \locs -> throwError (err, locs)

type TyCheck p = TyCheckT Identity

runTyCheckT :: Functor f => TyCheckT f a -> VarCtx -> ExceptT (TypeError, ErrorTrace) f a
runTyCheckT fa ctx = fmap fst . flip runStateT ctx . unTyCheckM $ fa

runTyCheck :: TyCheck p a -> VarCtx -> Either (TypeError, ErrorTrace) a
runTyCheck m = runExcept . runTyCheckT m

withScope :: MonadState s m => (s -> s) -> m a -> m a
withScope f m = do
  oldCtx <- get
  put (f oldCtx)
  result <- m
  put oldCtx
  pure result

resolveType :: Monad m => UType -> TyCheckT m UType
resolveType (RType v t ()) =
  RType v
    <$> fromMaybeM (typeError (TyErrInvalidType t)) (gets (deltaResolveSkel t . ctxDelta))
    <*> pure ()

typecheckFunBody :: Monad m => [(Text, UType)] -> [Stmt ()] -> TyCheckT m VarCtx
typecheckFunBody args stmts = do
  args' <- forM args (\(x, t) -> (x,) . rtypeSkel <$> resolveType t)
  withScope (varCtxModify (Map.fromList args' `Map.union`)) $
    traverse_ typecheckStmt stmts >> get

getVarType :: Monad m => Text -> TyCheckT m USkel
getVarType x = fromMaybeM (typeError (TyErrUnknownVar x)) (gets (varCtxLookup x))

assertTyEq :: Monad m => USkel -> USkel -> TyCheckT m ()
assertTyEq expTy actTy =
  if skelEq expTy actTy
  then pure ()
  else typeError $ TyErrMismatch expTy actTy

assertTySubty :: Monad m => USkel -> USkel -> TyCheckT m ()
assertTySubty t1 t2
  | TyInt Nothing <- t1, TyInt _ <- t2 = pure ()
  | TyInt (Just n) <- t1, TyInt (Just m) <- t2 =
      if n <= m then pure () else typeError (TyErrMismatch t2 t1)
  | TyArray t1' m <- t1, TyArray t2' n <- t2, t1' == t2' =
      case (m, n) of
        (_, Nothing) -> pure ()
        (Just m', Just n') | m' <= n' -> pure ()
        _ -> typeError (TyErrMismatch t2 t1)
  | otherwise = assertTyEq t2 t1


assertTyInt :: Monad m => USkel -> TyCheckT m (Maybe Int)
assertTyInt ty
  | TyInt m1 <- ty = pure m1
  | otherwise = typeError $ TyErrMismatch (TyInt Nothing) ty

-- | Assert that a variable is not being redefined.
assertNotRedef :: Monad m => Text -> TyCheckT m ()
assertNotRedef x =
  whenM (gets (Map.member x . ctxVars)) (typeError (TyErrRedef x))

-- | Assert that a function/struct name is not being redefined.
assertDeclNotRedef :: Monad m => Text -> TyCheckT m ()
assertDeclNotRedef x = do
  isStruct <- gets (Map.member x . delta_structs . ctxDelta)
  isFun <- gets (Map.member x . delta_funs . ctxDelta)
  when (isStruct || isFun) (typeError (TyErrRedef x))

-- | Assert that the type can be defined as a local variable
assertValidInBody :: Monad m => Text -> USkel -> TyCheckT m ()
assertValidInBody _x ty = case ty of
  _ -> pure ()
  -- where
  --   no = typeError $ TyErrInvalidDef x ty

assertArgCount :: Monad m => Int -> Int -> TyCheckT m ()
assertArgCount expN actN =
  unless (expN == actN) (typeError (TyErrArgCount expN actN))

-- | Typecheck the contract, returning the global environment.
typecheckContract :: Monad m => Contract () -> TyCheckT m (Delta ())
typecheckContract (Contract _ decls) = do
  let (varDecls, structDecls, funDecls) = flip foldMap decls $ \case
        d@DVar{} -> ([d], [], [])
        d@DStruct{} -> ([], [d], [])
        d -> ([], [], [d])
  -- Before type checking structs, insert the definitions
  modify $ \c ->
    let d = ctxDelta c
        snames = flip fmap structDecls $ \case
          DStruct n _ -> n
          _ -> undefined
    in
      c{ctxDelta = d{delta_structs=Map.union (Map.fromList [(s, []) | s <- snames]) (delta_structs d)}}
  traverse_ typecheckDecl structDecls
  traverse_ typecheckDecl varDecls
  -- Add functions declarations
  forM_ funDecls $ \case
    DFun{dfun_name=name, dfun_args=args, dfun_res=res, dfun_mut=mut} -> do
      assertDeclNotRedef name
      modify (\c -> let d = ctxDelta c in
                 c{ctxDelta = d{delta_funs=Map.insert name (args, res, mut) (delta_funs d)}})
    _ -> pure ()
  traverse_ typecheckDecl funDecls
  gets ctxDelta

typecheckDecl :: Monad m => Decl () -> TyCheckT m ()
typecheckDecl = \case
  DVar x ty me loc -> do
    assertDeclNotRedef x
    ty' <- rtypeSkel <$> resolveType ty
    modify (varCtxModify (Map.insert x ty'))
    modify (\ctx -> ctx{ctxLocs = Map.insert loc ty' (ctxLocs ctx)})
    forM_ me typecheckExpr
  DFun {dfun_args=args, dfun_res=res, dfun_body=body} -> do
    withScope (varCtxModify (Map.fromList [(x, rtypeSkel t) | (x, t) <- res] `Map.union`)) $
      typecheckFunBody args (blockStmts body) >> pure ()
  DCtor {dctor_args=args, dctor_body=body} ->
    typecheckFunBody args (blockStmts body) >> pure ()
  DAnnot a -> typecheckAnnot False a
  DStruct {dsct_name=name, dsct_fields=flds} -> do
    assertNotRedef name
    flds' <- forM flds $ (\(x, t) -> (x,) <$> resolveType t)
    modify (\c -> let d = ctxDelta c in
               c{ctxDelta = d{delta_structs=Map.insert name flds' (delta_structs d)}})

typecheckStmt :: Monad m => Stmt () -> TyCheckT m ()
typecheckStmt = addTrace $ \case
  SDecl x ty_ me -> do
    assertNotRedef x
    ty <- rtypeSkel <$> resolveType ty_
    assertValidInBody x ty
    modify (varCtxModify (Map.insert x ty))
    forM_ me (typecheckStmt . SAsn (LvVar x))
  SAsn lv e2 -> do
    ty2 <- typecheckExpr e2
    ty1 <- typecheckLvalue lv
    assertTySubty ty2 ty1
  SCall decls name args -> do
    structM <- gets (Map.lookup name . delta_structs . ctxDelta)
    funM <- gets (Map.lookup name . delta_funs . ctxDelta)
    retTys <-
      if | name `elem` ["assume", "assert", "require"] ->
             case args of
               [e] -> do
                 ty <- typecheckExpr e
                 assertTyEq TyBool ty
                 pure [TyUnit]
               _ -> typeError $ TyErrArgCount 1 (length args)
         | Just flds <- structM -> do
             assertArgCount (length flds) (length args)
             let (_, fldTys) = unzip flds
             forM_ (args `zip` fldTys) $ \(e, t) -> typecheckExpr e >>= assertTyEq (rtypeSkel t)
             pure [TyStruct name flds]
         | Just (fargs, frets, _) <- funM -> do
             eTys <- traverse typecheckExpr args
             -- Check arguments
             traverse_ (uncurry assertTySubty) (eTys `zip` (rtypeSkel . snd <$> fargs))
             pure (rtypeSkel . snd <$> frets)
         | name == "$__array_push" ->
             case args of
               [ea, eitem] -> do
                 ta <- typecheckExpr ea
                 case ta of
                   TyArray ti Nothing -> do
                     typecheckExpr eitem >>= assertTyEq ti
                     pure [TyArray ti Nothing]
                   _ -> typeError $ TyErrExpArray ta Nothing
               _ -> typeError $ TyErrArgCount 1 (length args)
         | name == "$__array_pop" ->
             case args of
               [ea] -> do
                 ta <- typecheckExpr ea
                 case ta of
                   TyArray ti Nothing -> pure [TyArray ti Nothing]
                   _ -> typeError $ TyErrExpArray ta Nothing
               _ -> typeError $ TyErrArgCount 1 (length args)
         | otherwise -> typeError $ TyErrUnknownVar name
    forM_ (decls `zip` retTys) $ \((x, ty_), rt) -> do
      assertNotRedef x
      ty <- rtypeSkel <$> resolveType ty_
      assertTyEq ty rt
      modify (varCtxModify (Map.insert x ty))
  SIf _ e b1 b2 -> do
    ty <- typecheckExpr e
    assertTyEq TyBool ty
    withScope id (traverse_ typecheckStmt (blockStmts b1))
    withScope id (traverse_ typecheckStmt (blockStmts b2))
  SWhile _ e b2 -> do
    ty <- typecheckExpr e
    assertTyEq TyBool ty
    withScope id (traverse_ typecheckStmt (blockStmts b2))
  SFetch{} -> error "Typecheck: unexpected fetch"
  SCommit{} -> error "Typecheck: unexpected commit"
  SAnnot a -> typecheckAnnot True a
  SReturn es -> traverse_ typecheckExpr es
  SHavoc -> pure ()
  SAbort -> pure ()
  where
    addTrace f s = do
      trace <- gets ctxErrLoc
      modify (\c -> c{ctxErrLoc = Left s : trace})
      ty <- f s
      modify (\c -> c{ctxErrLoc = trace})
      pure ty

typecheckConst :: Monad m => Constant -> TyCheckT m USkel
typecheckConst = \case
  CInt _ -> pure (TyInt Nothing)
  CByte _ -> pure TyByte
  CAddress _ -> pure TyAddress
  CBool _ -> pure TyBool
  CMapZero bt1 bt2 -> pure (TyMapping bt1 bt2)
  CArrZero bt1 msz -> pure (TyArray bt1 msz)
  CStruct name flds ->
    TyStruct name <$> (forM flds $ \(x, c) -> (x,) . (\t -> RType "v" t ())<$> typecheckConst c)
  CString s ->
    let size = ByteString.length (Data.Text.Encoding.encodeUtf8 s) in
      pure (TyArray TyByte (Just (toInteger size)))

typecheckLvalue :: Monad m => LValue -> TyCheckT m USkel
typecheckLvalue = typecheckExpr . lvalueToExpr

typecheckExpr :: Monad m => Expr -> TyCheckT m USkel
typecheckExpr = addTrace $ \case
  EConst c -> typecheckConst c
  EVar x -> getVarType x
  EArith2 _ e1 e2 -> do
    m1 <- typecheckExpr e1 >>= assertTyInt
    m2 <- typecheckExpr e2 >>= assertTyInt
    pure (TyInt (skelIntMerge m1 m2))
  EBoolOp bop -> do
    case bop of
      BAnd e1 e2 -> do
        typecheckExpr e1  >>= assertTyEq TyBool
        typecheckExpr e2  >>= assertTyEq TyBool
      BOr e1 e2 -> do
        typecheckExpr e1  >>= assertTyEq TyBool
        typecheckExpr e2  >>= assertTyEq TyBool
      BNot e1 -> typecheckExpr e1  >>= assertTyEq TyBool
    pure TyBool
  ERel rel e1 e2 -> do
    case rel of
      r | r == RelEq || r == RelNeq -> do
        t1 <- typecheckExpr e1
        t2 <- typecheckExpr e2
        assertTyEq t1 t2
      _ -> do
        _ <- typecheckExpr e1 >>= assertTyInt
        _ <- typecheckExpr e2 >>= assertTyInt
        pure ()
    pure TyBool
  EMapInd em ei -> do
    tm <- typecheckExpr em
    ti <- typecheckExpr ei
    (tkey, tval) <- case tm of
      TyMapping tk tv -> pure (Just tk, tv)
      TyArray t _ -> assertTyInt ti *> pure (Nothing, t)
      _ -> typeError $ TyErrExpMapping tm ti Nothing
    mapM_ (flip assertTyEq ti) tkey
    pure tval
  EMapPut em ei ev -> do
    tm <- typecheckExpr em
    ti <- typecheckExpr ei
    tv <- typecheckExpr ev
    (tkey, tval) <- case tm of
      TyMapping a b -> pure (Just a, b)
      TyArray a _ -> assertTyInt ti *> pure (Nothing, a)
      _ -> typeError $ TyErrExpMapping tm ti (Just tv)
    mapM_ (flip assertTyEq ti) tkey
    assertTyEq tval tv
    pure tval
  EField e f -> do
    ty <- typecheckExpr e
    delta <- gets ctxDelta
    case ty of
      TyStruct name _
        | Just flds <- Map.lookup name (delta_structs delta)
        , Just (_, RType _ t _) <- listToMaybe [p | p@(n, _) <- flds, n == f] ->
          pure t
      TyArray{} | f == "length" -> pure (TyInt (Just 256))
      _ -> typeError $ TyErrUnknownField ty f
  EFieldUpd e f _ -> do
    -- This should only appear after SSA, so no need to check thoroughly.
    te <- typecheckExpr e
    -- titem <- typecheckExpr ef
    if | TyArray ta _ <- te, f == "length" ->
         pure (TyArray ta Nothing)
       | otherwise -> undefined
  EUnintFn n es -> case n of
    "sum" -> case es of
      [e] -> do
        typecheckExpr e >>= \case
          TyMapping _ t@TyInt{} -> pure t
          TyArray t@TyInt{} _ -> pure t
          _ ->  typeError $ TyErrExpArray (TyInt Nothing) Nothing
      _ -> assertArgCount 1 (length es) >> undefined
    "sumTo" -> case es of
      [ea, ei] -> do
        _ <- typecheckExpr ea >>= assertTyInt
        _ <- typecheckExpr ei >>= assertTyInt
        pure (TyInt Nothing)
      _ -> assertArgCount 1 (length es) >> undefined
    _ -> typeError $ TyErrUnknownVar n
  EHavoc ty -> pure ty
  ECast e ty -> typecheckExpr e *> pure ty
  where
    addTrace f e = do
      trace <- gets ctxErrLoc
      modify (\c -> c{ctxErrLoc = Right e : trace})
      ty <- f e
      modify (\c -> c{ctxErrLoc = trace})
      pure ty

typecheckAnnot :: Monad m => Bool -> Annot -> TyCheckT m ()
typecheckAnnot inBody = \case
  ASubtype x _skel -> do
    xty <- getVarType x
    when inBody (assertValidInBody x xty)
    -- TODO: typecheck skel
  AAscribe x _skel -> do
    _xty <- getVarType x
    -- TODO: run sort check
    pure ()
  AAssume _ ->
    -- TODO: run sort check
    pure ()
  AReachable -> pure ()
  APhiReorder{} -> pure ()
  ADefQual{} -> when inBody (typeError TyErrQualInBody)
