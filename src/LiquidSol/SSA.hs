{-# LANGUAGE OverloadedStrings, FlexibleContexts, ScopedTypeVariables #-}

module LiquidSol.SSA
  ( RenameTable(..), rtableEmpty
  , RenameT(..), runRenameT, evalRenameT, runRename, evalRename, withScope
  , replaceName, renameAssign, renameNewLocal
  , indexedName
  , ssaTransform) where

import Control.Monad.Extra (concatMapM, ifM)
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Text (Text)
import qualified Data.Text as Text
import Data.List (partition)
import Data.Map.Strict (Map)
import qualified Data.Map.Merge.Strict as Map
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Functor.Identity

import LiquidSol.Syntax
import LiquidSol.AstAnalysis (scanAssigns)
import LiquidSol.Util.Unsafe
import LiquidSol.LiquidTypes (solidityGlobalVars)
import Data.Bifunctor (second)

type VarMap = Map Text Int

-- | SSA renaming state. Keeps state for local variables, while ignoring storage
-- (global) variable mutation.
data RenameTable = RTable
  { renameMap :: VarMap
  , renameCounter :: Map Text Int
  , renameGlobal :: Set Text -- ^ Global variables to avoid SSA transforms on
  , renameTypeAnn :: Map Text UType
  , renameDepVars :: Set Text -- ^ Bound dependent variables (to ignore)
  , renameInBody :: Bool -- ^ Whether currently in a function body
  , renameStructs :: Map Text (Map Text USkel)
  }
  deriving (Show, Eq, Ord)

rtableEmpty :: RenameTable
rtableEmpty = RTable { renameMap = Map.empty
                     , renameCounter = Map.empty
                     , renameGlobal = Set.empty
                     , renameTypeAnn = Map.empty
                     , renameDepVars = Set.empty
                     , renameInBody = False
                     , renameStructs = Map.empty }

-- rtableGetGlobal :: Int -> RenameTable -> Maybe Type
-- rtableGetGlobal l = Map.lookup l . renameGlobal

newtype RenameT m a = RenameM
  { unRenameM :: StateT RenameTable m a }
  deriving (Functor, Applicative, Monad,
            MonadState RenameTable)

type Rename = RenameT Identity

runRenameT :: RenameT f a -> RenameTable -> f (a, RenameTable)
runRenameT fa ctx = flip runStateT ctx . unRenameM $ fa

evalRenameT :: Functor f => RenameT f a -> RenameTable -> f a
evalRenameT fa = fmap fst . runRenameT fa

runRename :: Rename a -> RenameTable -> (a, RenameTable)
runRename m = runIdentity . runRenameT m

evalRename :: Rename a -> RenameTable -> a
evalRename m = fst . runRename m

withScope :: Monad m => RenameT m a -> RenameT m (a, VarMap)
withScope m = do
  isBody <- gets renameInBody
  curMap <- gets renameMap
  modify (\r -> r { renameInBody = True })
  result <- m
  newMap <- gets renameMap
  modify (\r -> r { renameMap = curMap, renameInBody = isBody })
  pure (result, newMap)

-- | Replaces the unrenamed variable with its current name (generating a fresh
-- name if necessary).
replaceName :: Monad m => Text -> RenameT m Text
replaceName x =
  -- If this is a bound dependent variable or we're not in a function, do nothing.
  ifM (gets (\r -> (Set.member x (renameDepVars r)) || not (renameInBody r)
            || Map.member x globalVars)) (pure x) $
  -- Otherwise, replace the name
    gets (Map.lookup x . renameMap) >>= \case
      Just i -> pure (indexedName x i)
      Nothing -> renameNewLocal x
  where
    globalVars = Map.fromList solidityGlobalVars :: Map Text UType

-- | Generate a fresh name for the given variable if it is a local variable.
renameAssign :: Monad m => Text -> RenameT m Text
renameAssign = renameNewLocal

-- | Generate a fresh name for the given local variable and set the current
-- instance of the variable to the fresh name.
renameNewLocal :: Monad m => Text -> RenameT m Text
renameNewLocal x = do
  newId <- gets (maybe 0 (+1) . Map.lookup x . renameCounter)
  modify (\r -> r { renameCounter = Map.insert x newId (renameCounter r)
                  , renameMap = Map.insert x newId (renameMap r) })
  pure (indexedName x newId)

indexedName :: Text -> Int -> Text
indexedName x i = x <> "$" <> Text.pack (show i)

ssaTransform :: Contract () -> (Contract (), RenameTable)
ssaTransform c = runRename (transformContract c) rtableEmpty

transformContract :: Monad m => Contract () -> RenameT m (Contract ())
transformContract (Contract name decls) = do
  let structs = flip concatMap decls $ \case
        DStruct n flds -> [(n, flds)]
        _ -> []
  modify (\st -> st{renameStructs = Map.map (Map.fromList . fmap (second rtypeSkel))
                     (Map.fromList structs) })
  let (varDecls, funDecls) = flip partition decls $ \case
        DVar{} -> True
        _ -> False
  newDecls <- traverse transformDecl (varDecls ++ funDecls)
  pure (Contract name newDecls)

transformDecl :: Monad m => Decl () -> RenameT m (Decl ())
transformDecl = \case
  d@(DVar x _ _ _) -> do
    modify (\r -> r { renameGlobal = Set.insert x (renameGlobal r)})
    pure d
  d@(DFun{dfun_args=args, dfun_res=res, dfun_body=body, dfun_loc=loc}) -> do
    ((newArgs, newRes, newBody), _) <- withScope (transformFunBody loc args res body)
    pure (d{dfun_args=newArgs, dfun_res=newRes, dfun_body=newBody})
  DCtor {dctor_args=args, dctor_body=body, dctor_loc=loc} -> do
    ((newArgs, _, newBody), _) <- withScope (transformFunBody loc args [] body)
    pure (DCtor {dctor_args=newArgs, dctor_body=newBody})
  DAnnot annot -> do
    annot' <- transformAnnot annot
    pure (DAnnot annot')
  d@DStruct{} -> pure d

transformFunBody :: Monad m
                 => SrcLoc
                 -> [(Text, UType)]
                 -> [(Text, UType)]
                 -> Block ()
                 -> RenameT m ([(Text, UType)], [(Text, UType)], Block ())
transformFunBody loc args res body = do
  let mkParam (x, ty) = do
        modify (\r -> r { renameTypeAnn = Map.insert x ty (renameTypeAnn r) })
        x' <- renameNewLocal x
        pure (x', ty)
  newArgs <- forM args mkParam
  -- zero initialize the return variables
  retInitStmts <- forM res $ \(x, ty) -> do
    (x', ty') <- mkParam (x, ty)
    pure $ (loc, SDecl x' ty' (Just (EConst (zeroValue (rtypeSkel ty')))))
  newBlock <- traverseBlock transformStmt body
  -- Create the final return values here:
  finalRes <- forM res $ \(x, ty) -> do
    curName <- replaceName x
    pure (curName, ty)
  pure (newArgs, finalRes, retInitStmts <> newBlock)

transformBlock :: Monad m => Block () -> RenameT m (Block (), Bool)
transformBlock stmts =
  let (stmts', earlyStop) = takeUntilReturn stmts in
    (,earlyStop) <$> traverseBlock transformStmt stmts'

transformStmt :: Monad m => Stmt () -> RenameT m [Stmt ()]
transformStmt = \case
  SDecl x ty me -> do
    me' <- traverse transformExpr me
    x' <- renameNewLocal x
    modify (\r -> r { renameTypeAnn = Map.insert x ty (renameTypeAnn r) })
    emit $ SDecl x' ty me'
  SAsn lv e -> do
    e' <- transformExpr e
    let x = lvalueFirst lv
    oldX <- replaceName x
    x' <- renameAssign x
    if x' == x
      then emit $ SAsn lv e' -- Global name, do not create new declaration
      else do
        {-
          This is where things get interesting. We need to transform
            e[i].f = foo;
          into
            type e0 = e[i][f := foo];
            type e' = e[i := e0];

          Assignments to unknown variables will be caught by the type checker.
          Assume that the type is added during the walk.
        -}

        -- First, set the type of the final value.
        ty <- gets ((`unsafeLookup` x) . renameTypeAnn)
        modify (\r -> r { renameTypeAnn = Map.insert x' ty (renameTypeAnn r) })

        -- Now walk up the LValue chain from right to left, updating the RHS and
        -- generating intermediate declarations. (CPS style)
        let walkLv :: Monad m
                   => Expr -- ^ rhs
                   -> LValue -- ^ lvalue snoc
                   -> RenameT m ([Stmt ()], Expr, USkel)
            walkLv rhs = \case
              LvVar{} ->
                -- Must be oldX.
                pure ([SDecl x' ty (Just rhs)], EVar oldX, rtypeSkel ty)
              LvInd lsnoc ei -> do
                -- Generate the intermediate variable name, then go to the outer access.
                tmpName <- renameNewLocal ("__tmp!!" <> x')
                ei' <- transformExpr ei
                (stmts, el, lskel) <- walkLv (EVar tmpName) lsnoc
                let t = case lskel of
                      TyMapping _ t2 -> t2
                      TyArray t2 _ -> t2
                      _ -> error $ "assigning to index of non-array/mapping: " <> show lsnoc <> " (type: " <> show lskel <> ")"
                -- Now we return to the inner access, so prepend our declaration.
                let lty = RType "v" lskel ()
                modify (\r -> r { renameTypeAnn = Map.insert ("__tmp!!" <> x') lty (renameTypeAnn r) })
                let decl = SDecl tmpName lty (Just (EMapPut el ei' rhs))
                pure (decl : stmts, EMapInd el ei', t)
              LvFld lsnoc f -> do
                -- Generate the intermediate variable name, then go to the outer access.
                tmpName <- renameNewLocal ("__tmp!!" <> x')
                (stmts, el, lskel) <- walkLv (EVar tmpName) lsnoc
                structs <- gets renameStructs
                let t = case lskel of
                      TyStruct n _
                        | Just flds <- Map.lookup n structs
                        , Just t2 <- Map.lookup f flds -> t2
                      TyArray t2 _ -> t2
                      _ -> error $ "assigning to field of non-struct: " <> show lv <> " (type: " <> show lskel <> ")"
                -- Now we return to the inner access, so prepend our declaration.
                let lty = RType "v" lskel ()
                modify (\r -> r { renameTypeAnn = Map.insert ("__tmp!!" <> x') lty (renameTypeAnn r) })
                let decl = SDecl tmpName lty (Just (EFieldUpd el f rhs))
                pure (decl : stmts, EField el f, t)
        (stmts, _, _) <- walkLv e' lv
        pure stmts
  SCall me name args -> do
    me' <- forM me $ \(x, ty) -> do
      x' <- replaceName x
      modify (\r -> r { renameTypeAnn = Map.insert x ty (renameTypeAnn r) })
      pure (x', ty)
    args' <- traverse transformExpr args
    emit $ SCall me' name args'
  SIf _ e b1 b2 -> do
    e' <- transformExpr e
    ((b1', hasReturn1), vm1) <- withScope (transformBlock b1)
    ((b2', hasReturn2), vm2) <- withScope (transformBlock b2)
    let newStmt phi = SIf phi e' b1' b2'
    phiVars <- if | hasReturn1 && not (hasReturn2) -> pure (Map.map pure vm2)
                  | hasReturn2 && not (hasReturn1) -> pure (Map.map pure vm1)
                  | otherwise -> mergeVarMaps vm1 vm2
    if Map.null phiVars
      then emit (newStmt [])
      else do
        phiNodes <- forM (Map.toList phiVars) $ \(x, args) -> do
          let lookupWithMsg t = case Map.lookup x t of
                Just a -> a
                Nothing -> error $ "Could not find " <> show x <> " in scope"
          ty <- gets (lookupWithMsg . renameTypeAnn)
          x' <- renameAssign x
          modify (\r -> r { renameTypeAnn = Map.insert x' ty (renameTypeAnn r) })
          pure (x', ty, [indexedName x i | i <- args])
        emit (newStmt phiNodes)
  SWhile _ e block -> do
    vm1 <- gets renameMap
    -- Scan block for assignments first so we know which variables need phi nodes
    let blockAssigns = mconcat (scanAssigns <$> blockStmts block)
    let toInsert = Set.toList $ blockAssigns `Set.intersection` Map.keysSet vm1
    -- Generate phi node variables; we'll place the nodes later. Note that the
    -- header phi nodes are available in scope to statements after the while
    -- loop.
    headerPhiVars <- forM toInsert $ \x -> do
      ty <- gets ((\t -> t `unsafeLookup` x) . renameTypeAnn)
      x' <- renameAssign x
      modify (\r -> r { renameTypeAnn = Map.insert x' ty (renameTypeAnn r) })
      pure (x', ty)
    ((e', block'), vm2) <- withScope $ do
      -- Rewrite the guard
      e' <- transformExpr e
      -- SSA transform body
      nb <- traverseBlock transformStmt block
      pure (e', nb)
    -- The header of the loop dominates itself so place phi nodes there. Phi
    -- nodes after the loop are not needed since the header phi nodes are not
    -- assigned to in the condition check.
    phiVars <- mergeVarMaps vm1 vm2
    let headerPhiMap = Map.fromList (toInsert `zip` headerPhiVars)
    phiNodes <- forM (Map.keys phiVars) $ \x -> do
      let args = phiVars `unsafeLookup` x
      let (xBody, ty) = headerPhiMap `unsafeLookup` x
      let phiArgs = [indexedName x i | i <- args]
      pure (xBody, ty, phiArgs)
    let newStmt = SWhile phiNodes e' block'
    pure [newStmt]
  SFetch fs _ -> do
    -- Every fetch, regardless if it is declaration or assignment, will be
    -- transformed into a declaration.
    fs' <- forM fs $ \(x, ty, l) -> do
      x' <- renameNewLocal x
      modify (\r -> r { renameTypeAnn = Map.insert x ty (renameTypeAnn r) })
      pure (x', ty, l)
    pure [SFetch fs' True]
  SCommit cs ->
    let mkCs' = forM cs $ \(l, e) -> do
          e' <- transformExpr e
          pure (l, e')
    in
    pure . SCommit <$> mkCs'
  SAnnot annot -> do
    annot' <- transformAnnot annot
    pure [SAnnot annot']
  SReturn es -> do
    es' <- traverse transformExpr es
    pure [SReturn es']
  SHavoc -> pure [SHavoc]
  SAbort -> pure [SAbort]
  where
    emit :: Monad m => Stmt p -> RenameT m [Stmt p]
    emit s = pure [s]

    mergeVarMaps :: Monad m => VarMap -> VarMap -> RenameT m (Map Text [Int])
    mergeVarMaps vm1 vm2 =
      let phiMergeF x n1 n2 =
            if n1 == n2
            then pure Nothing
            else do
              let merged = pure (Just [n1, n2])
              ifM (gets (Map.member x . renameMap)) merged (pure Nothing)
      in Map.mergeA Map.dropMissing Map.dropMissing (Map.zipWithMaybeAMatched phiMergeF) vm1 vm2

transformExpr :: Monad m => Expr -> RenameT m Expr
transformExpr = \case
  e@(EConst _) -> pure e
  EVar x -> EVar <$> replaceName x
  EArith2 op e1 e2 -> EArith2 op <$> recur e1 <*> recur e2
  EBoolOp bop -> EBoolOp <$> case bop of
    BAnd e1 e2 -> bin BAnd e1 e2
    BOr e1 e2 -> bin BOr e1 e2
    BNot e1 -> BNot <$> recur e1
  ERel rel e1 e2 -> ERel rel <$> recur e1 <*> recur e2
  EMapInd em ei -> EMapInd <$> recur em <*> recur ei
  e@EMapPut{} -> pure e
  EField e f -> EField <$> recur e <*> pure f
  EFieldUpd e f ef -> EFieldUpd <$> recur e <*> pure f <*> recur ef
  EUnintFn n es -> EUnintFn n <$> traverse recur es
  e@EHavoc{} -> pure e
  ECast e ty -> ECast <$> recur e <*> pure ty
  where
    recur = transformExpr
    bin op e1 e2 = op <$> recur e1 <*> recur e2

transformAnnot :: Monad m => Annot -> RenameT m Annot
transformAnnot = \case
  ASubtype x t -> ASubtype <$> replaceName x <*> transformRType t
  AAscribe x t -> AAscribe <$> replaceName x <*> transformRType t
  AAssume p -> AAssume <$> transformPred p
  AReachable -> pure AReachable
  APhiReorder xs -> APhiReorder <$> traverse replaceName xs
  a@ADefQual{} -> pure a
  where
    transformFlds [] = pure []
    transformFlds ((x, t):next) = withFreshVar x $ do
      t' <- transformRType t
      ((x, t'):) <$> transformFlds next

    transformRType :: Monad m => RType Pred -> RenameT m (RType Pred)
    transformRType (RType x t p) =
      withFreshVar x (RType x <$> transformSkel t <*> transformPred p)

    transformSkel :: Monad m => Skel Pred -> RenameT m (Skel Pred)
    transformSkel = \case
      TyInt m -> pure (TyInt m)
      TyBool -> pure TyBool
      TyUnit -> pure TyUnit
      TyAddress -> pure TyAddress
      TyByte -> pure TyByte
      TyFunc x ty1 ty2 -> withFreshVar x (TyFunc x <$> transformRType ty1 <*> transformRType ty2)
      TyStruct name flds -> TyStruct name <$> transformFlds flds
      TyArray t msz -> (\t' -> TyArray t' msz) <$> transformSkel t
      TyMapping t1 t2 -> TyMapping <$> transformSkel t1 <*> transformSkel t2

withFreshVar :: Monad m => Text -> RenameT m a -> RenameT m a
withFreshVar x m = do
  notBound <- gets (not . Set.member x . renameDepVars)
  when notBound $ modify (\r -> r{renameDepVars = Set.insert x (renameDepVars r)})
  result <- m
  when notBound $ modify (\r -> r{renameDepVars = Set.delete x (renameDepVars r)})
  pure result

transformPred :: Monad m => Pred -> RenameT m Pred
transformPred = \case
  e@(PConst _) -> pure e
  PVar x -> PVar <$> replaceName x
  PArith2 op e1 e2 -> PArith2 op <$> recur e1 <*> recur e2
  PRel rel e1 e2 -> PRel rel <$> recur e1 <*> recur e2
  PAnd e1 e2 -> bin PAnd e1 e2
  POr e1 e2 -> bin POr e1 e2
  PNot e1 -> PNot <$> recur e1
  PImplies p q -> PImplies <$> transformPred p <*> transformPred q
  PIff p q -> PIff <$> transformPred p <*> transformPred q
  PMapInd em ei -> PMapInd <$> recur em <*> recur ei
  e@PMapPut{} -> pure e
  PField e f -> PField <$> recur e <*> pure f
  PFieldUpd e f ef -> PFieldUpd <$> recur e <*> pure f <*> recur ef
  PUnintFn n es -> PUnintFn n <$> traverse recur es
  e@PHavoc{} -> pure e
  PCast e ty -> PCast <$> recur e <*> pure ty
  where
    recur = transformPred
    bin op e1 e2 = op <$> recur e1 <*> recur e2
