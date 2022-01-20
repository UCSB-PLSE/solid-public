{-# LANGUAGE OverloadedStrings, FlexibleContexts, ScopedTypeVariables #-}

module LiquidSol.StoreTransform
  ( storeTransform ) where

import Control.Monad (when, forM)
import Control.Monad.Extra (concatMapM)
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Data.Functor.Identity
import Data.Bifunctor (second)
import Data.Maybe (maybeToList)
import Data.Text (Text)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as Map
import qualified Data.Set as Set
import Data.Maybe (isJust)


import LiquidSol.AstAnalysis (allVarsStmt)
import LiquidSol.Syntax
import LiquidSol.LiquidTypes (delta_structs, deltaResolveSkel, deltaEmpty, Delta (delta_funs), PendingSub(psubVars), applyPendingSub)
import LiquidSol.Util.Unsafe (fromJust)

data TransCtx = TransCtx
  { tcGlobals :: !(Map Text UType) -- ^ Types of storage variables
  , tcLocs :: !(Map Text Int) -- ^ Location of each storage variable
  , tcCheckOut :: !(Map Int Text) -- ^ Checked out storage variables
  , tcRefCounter :: Int -- ^ Highest unallocated abstract location
  , tcCheckOutCount :: Int -- ^ Unique names for checkout
  , tcDelta :: Delta () -- ^ Global definition context (mainly for structs)
  }
  deriving (Show)

transCtxEmpty :: TransCtx
transCtxEmpty = TransCtx
  { tcGlobals = Map.empty
  , tcLocs = Map.empty
  , tcCheckOut = Map.empty
  , tcRefCounter = 0
  , tcCheckOutCount = 0
  , tcDelta = deltaEmpty }

newtype StoTransT m a = StoTransM { unTransM :: StateT TransCtx m a }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadState TransCtx)

type StoTrans a = StoTransT Identity a

runStoTransT :: StoTransT m a -> TransCtx -> m (a, TransCtx)
runStoTransT ma ctx = flip runStateT ctx . unTransM $ ma

runStoTrans :: StoTrans a -> TransCtx -> (a, TransCtx)
runStoTrans ma = runIdentity . runStoTransT ma

checkoutVar :: Monad m => Text -> StoTransT m ([Stmt ()], Text)
checkoutVar x = do
  -- fstmtM <- checkoutAll
  (x', _) <- checkoutVar_ x
  -- pure (maybeToList fstmtM, x')
  pure ([], x')

checkoutVar_ :: Monad m => Text -> StoTransT m (Text, Maybe (UType, Loc))
checkoutVar_ x = do
  lookupRes <- runMaybeT $ do
        ty <- MaybeT $ gets (Map.lookup x . tcGlobals)
        loc <- MaybeT $ gets (Map.lookup x . tcLocs)
        pure (ty, loc)
  case lookupRes of
    {-
    Just (ty, loc) ->  -- Global variable
      gets (Map.lookup loc . tcCheckOut) >>= \case
        Nothing -> do
          -- Not checked out yet, so check it out here
          -- TODO: Generate fresh name
          chkId <- gets tcCheckOutCount
          let xLocal = x <> "!" <> Text.pack (show chkId)
          modify (\c -> c { tcCheckOut = Map.insert loc xLocal (tcCheckOut c)
                          , tcCheckOutCount = chkId + 1 })
          pure (xLocal, Just (ty, Loc loc))
        Just xLocal ->
          pure (xLocal, Nothing) -- Replace with the checked out name
    Nothing -> pure (x, Nothing)  -- Local variable, noop
    -}
    _ -> pure (x, Nothing)

checkoutAll :: Monad m => StoTransT m (Maybe (Stmt ()))
checkoutAll = do
  glbls <- gets tcGlobals
  locs <- gets tcLocs
  let mergeF _ ty loc = Just (ty, Loc loc)
      merged = Map.merge Map.dropMissing Map.dropMissing (Map.zipWithMaybeMatched mergeF) glbls locs
  let fetched = [(x, ty, loc) | (x, (ty, loc)) <- Map.toList merged]
  pure $ if null fetched then Nothing else Just (SFetch fetched False)

storeTransform :: Delta() -> Contract () -> Contract ()
storeTransform delta c = fst $ runStoTrans (transformContract c) transCtxEmpty{tcDelta = delta}

partitionDecls :: [Decl ()] -> ([Decl ()], [Decl ()], [Decl ()], [Decl ()])
partitionDecls decls = foldMap sp decls
  where
    sp = \case
      d@DVar{} -> ([d], [], [], [])
      d@DStruct{} -> ([], [d], [], [])
      d@DCtor{} -> ([], [], [d], [])
      d -> ([], [], [], [d])

transformContract :: Monad m => Contract () -> StoTransT m (Contract ())
transformContract (Contract name decls) = do
  -- Transform storage variable declarations
  (varDecls, structDecls, ctors, otherDecls) <- (partitionDecls <$>) $ forM decls $ \case
        DVar x ty me _ -> do
          when (isJust me) (error "storeTransform: declaration of storage variable has assignment")
          loc <- gets tcRefCounter
          modify (\c -> c { tcGlobals = Map.insert x ty (tcGlobals c)
                          , tcLocs = Map.insert x loc (tcLocs c)
                          , tcRefCounter = loc + 1 })
          pure (DVar x ty Nothing (Loc loc))
        d -> pure d
  -- Find constructor
  ctor' <- traverse transformDecls $ case ctors of
    (d : _) -> Just d
    [] -> if null varDecls then Nothing else Just (DCtor{dctor_args=[], dctor_body=[], dctor_loc=noSrcLoc})

  -- Transform function declarations
  otherDecls' <- traverse transformDecls otherDecls
  pure (Contract name (structDecls ++ varDecls ++ maybeToList ctor' ++ otherDecls'))

transformDecls :: Monad m => Decl () -> StoTransT m (Decl ())
transformDecls = \case
  d@(DFun {dfun_body=body, dfun_loc=loc}) -> do
    -- Fetch the variables. Note that this will generate an invalid program,
    -- since it will redeclare the globals.
    body' <- mkFun body True loc
    pure (d{dfun_body=body'})
  d@DCtor {dctor_body=body, dctor_loc=loc} -> do
    -- Assign every storage variable to zero in the body to "initialize" them.
    glbls <- gets tcGlobals
    delta <- gets tcDelta
    let zeroInitStmts = [ (loc, SDecl x ty (Just (EConst zv)))
                        | (x, ty) <- Map.toList glbls
                        , let zv = zeroValue (fromJust (deltaResolveSkel (rtypeSkel ty) delta)) ]
    body' <- mkFun (zeroInitStmts <> body <> (if null glbls then [(loc, SCommit [])] else [])) False loc
    pure (d{dctor_body=body'})
  d -> pure d
  where
    mkFun body shouldFetch loc = do
      fetchStmt <- if shouldFetch then checkoutAll else pure Nothing
      newBody <- transformFunBody loc body
      pure $ maybe newBody (\fetchS -> (loc, fetchS):newBody) fetchStmt

commitPending :: Monad m => StoTransT m (Maybe (Stmt ()))
commitPending = do
  pending <- gets (Map.toList . tcLocs)
  pure $ if null pending
    then Nothing
    else Just $ SCommit [(Loc l, EVar x) | (x, l) <- pending]

{-
getCheckedOut :: Monad m => StoTransT m (Map Int Text)
getCheckedOut = gets tcCheckOut

clearCheckedOut :: Monad m => StoTransT m ()
clearCheckedOut = modify (\c -> c { tcCheckOut = Map.empty })
-}

transformFunBody :: Monad m => SrcLoc -> Block () -> StoTransT m (Block ())
transformFunBody loc stmts = do
  stmts' <- transformBlock stmts
  -- Commit pending and clear check out state
  commitStmt <- commitPending
  -- clearCheckedOut
  pure (stmts' ++ ((loc,) <$> maybeToList commitStmt))

transformBlock :: Monad m => Block () -> StoTransT m (Block ())
transformBlock b = traverseBlock transformStmt b

transformStmt :: Monad m => Stmt () -> StoTransT m [Stmt ()]
transformStmt = \case
  s@(SDecl _ _ Nothing) -> pure [s]
  SDecl x ty (Just e) -> do
    (fetchStmts, e') <- replaceGlobalRefs e
    pure (fetchStmts ++ [SDecl x ty (Just e')])
  SAsn lv e -> do
    (fetchStmts, e') <- replaceGlobalRefs e
    (fetchStmtsX, lv') <- replaceLvalueRefs lv
    pure (fetchStmts <> fetchStmtsX <> [SAsn lv' e'])
  SCall massign fname args -> do
    (fetchStmts, args') <- unzip <$> traverse replaceGlobalRefs args
    delta <- gets tcDelta
    (commit, fetchStmts2) <-
      if | fname `elem` ["assume", "require", "assert", "$__array_push", "$__array_pop"] ->
           pure (Nothing, Nothing)
         | Just (_, _, MutStateless) <- Map.lookup fname (delta_funs delta) ->
           pure (Nothing, Nothing)
         | Just _ <- Map.lookup fname (delta_structs delta) ->
           pure (Nothing, Nothing)
         | otherwise -> do
             cstmt <- commitPending
             -- horrible hack to not generate a fetch if function is readonly
             -- (even if previously committed)
             chkStmt <- case Map.lookup fname (delta_funs delta) of
               Just (_, _, MutReadonly) -> pure Nothing
               _ -> checkoutAll
             pure (cstmt, chkStmt)
    pure (mconcat fetchStmts <> maybeToList commit <> [SCall massign fname args'] <> maybeToList fetchStmts2)
  SIf phi e sThen sElse -> do
    -- Transform guard
    (fetchStmtsE, e') <- replaceGlobalRefs e
    -- Transform branches
    let mkBranch br = transformBlock br
    sThen' <- mkBranch sThen
    sElse' <- mkBranch sElse
    pure (fetchStmtsE ++ [SIf phi e' sThen' sElse'])
  SWhile phi e body -> do
    -- Transform guard
    (fetchStmtsE, e') <- replaceGlobalRefs e
    -- Transform body
    body' <- transformBlock body
    pure (fetchStmtsE ++ [SWhile phi e' body'])
  SAnnot annot -> case annot of
    -- TODO: need to properly substitute here
    ASubtype x (RType v ty p) -> do
      (fetchStmts1, x') <- checkoutVar x
      (fetchStmts2, skel') <- second (RType v ty) <$> replacePredRefs p
      pure (fetchStmts1 <> fetchStmts2 <> [SAnnot (ASubtype x' skel')])
    AAscribe x (RType v ty p) -> do
      (fetchStmts1, x') <- checkoutVar x
      (fetchStmts2, skel') <- second (RType v ty) <$> replacePredRefs p
      pure (fetchStmts1 <> fetchStmts2 <> [SAnnot (AAscribe x' skel')])
    AAssume p -> (\(stmts, p') -> stmts ++ [SAnnot (AAssume p')]) <$> replacePredRefs p
    AReachable -> pure [SAnnot AReachable]
    a -> pure [SAnnot a]
  SReturn es -> do
    (stmts, es') <- unzip <$> traverse replaceGlobalRefs es
    commitStmt <- commitPending
    pure (mconcat stmts <> maybeToList commitStmt <> [SReturn es'])
  SHavoc -> do
    commitStmt <- commitPending
    -- TODO: SSA needs to handle checked out variables as well in phi functions :/
    -- clearCheckedOut
    fetchStmt <- checkoutAll
    pure (maybeToList commitStmt <> [SHavoc] <> maybeToList fetchStmt)
  s -> pure [s]
  where
    stmtGlobals stmt = gets ((allVarsStmt stmt `Set.union`) . Map.keysSet . tcGlobals)

replaceGlobalRefs :: Monad m => Expr -> StoTransT m ([Stmt ()], Expr)
replaceGlobalRefs = \case
  e@EConst{} -> pure ([], e)
  EVar x -> second EVar <$> checkoutVar x
  EArith2 op e1 e2 -> bin (EArith2 op) e1 e2
  EBoolOp bop -> case bop of
    BAnd e1 e2 -> bin (\e1' e2' -> EBoolOp (BAnd e1' e2')) e1 e2
    BOr e1 e2 -> bin (\e1' e2' -> EBoolOp (BOr e1' e2')) e1 e2
    BNot e1 -> second (EBoolOp . BNot) <$> recur e1
  ERel r e1 e2 -> bin (ERel r) e1 e2
  EMapInd e1 e2 -> bin EMapInd e1 e2
  EMapPut{} -> error "storeTransform: unexpected EMapPut"
  EField e f -> second (\e' -> EField e' f) <$> recur e
  EFieldUpd e f ef -> bin (\e' ef' -> EFieldUpd e' f ef') e ef
  EUnintFn n es ->
    let f (accStmts, accEs) e = do
          (stmts, e') <- replaceGlobalRefs e
          pure (accStmts ++ stmts, accEs ++ [e'])
    in second (EUnintFn n) <$> foldM f ([], []) es
  e@EHavoc{} -> pure (mempty, e)
  ECast e ty -> second (\e' -> ECast e' ty) <$> recur e
  where
    recur = replaceGlobalRefs
    bin ctor p q = do
      (stmts1, p') <- recur p
      (stmts2, q') <- recur q
      pure (stmts1 ++ stmts2, ctor p' q')

replaceLvalueRefs :: Monad m => LValue -> StoTransT m ([Stmt ()], LValue)
replaceLvalueRefs = \case
  LvVar x -> second LvVar <$> checkoutVar x
  LvInd lsnoc ei -> do
    (stmts1, ei') <- replaceGlobalRefs ei
    (stmts2, lsnoc') <- replaceLvalueRefs lsnoc
    pure (stmts1 ++ stmts2, LvInd lsnoc' ei')
  LvFld lsnoc f -> second (flip LvFld f) <$> replaceLvalueRefs lsnoc

replacePredRefs :: Monad m => Pred -> StoTransT m ([Stmt ()], Pred)
replacePredRefs = \case
  e@PConst{} -> pure ([], e)
  PVar x -> second PVar <$> checkoutVar x
  PArith2 op e1 e2 -> bin (PArith2 op) e1 e2
  PAnd e1 e2 -> bin PAnd e1 e2
  POr e1 e2 -> bin POr e1 e2
  PNot e1 -> second PNot <$> recur e1
  PRel r e1 e2 -> bin (PRel r) e1 e2
  PMapInd e1 e2 -> bin PMapInd e1 e2
  PMapPut{} -> error "storeTransform: unexpected PMapPut"
  PField e f -> second (\e' -> PField e' f) <$> recur e
  PFieldUpd e f ef -> bin (\e' ef' -> PFieldUpd e' f ef') e ef
  PUnintFn n es ->
    let f (accStmts, accPs) e = do
          (stmts, e') <- recur e
          pure (accStmts ++ stmts, accPs ++ [e'])
    in second (PUnintFn n) <$> foldM f ([], []) es
  p@PHavoc{} -> pure (mempty, p)
  PCast p ty -> second (\p' -> PCast p' ty) <$> recur p
  where
    recur = replacePredRefs
    bin ctor p q = do
      (stmts1, p') <- recur p
      (stmts2, q') <- recur q
      pure (stmts1 ++ stmts2, ctor p' q')
