module LiquidSol.Solidity.ContextMonad where

import Control.Monad.State.Strict
import LiquidSol.Solidity.Internal.Syntax
import Data.Functor.Identity (Identity)
import qualified Data.HashMap.Strict as HashMap
import LiquidSol.Util.Unsafe
import Data.HashMap.Strict (HashMap)

newtype ContextT m a = ContextT { unContextT :: StateT SourceCtx m a }
  deriving (Functor, Applicative, Monad, MonadTrans)

putContext :: Monad m => SourceCtx -> ContextT m ()
putContext = ContextT . put

getContext :: Monad m => ContextT m SourceCtx
getContext = ContextT get

getsContext :: Monad m => (SourceCtx -> a) -> ContextT m a
getsContext f = ContextT (gets f)

modifyContext :: Monad m => (SourceCtx -> SourceCtx) -> ContextT m ()
modifyContext = ContextT . modify

type Context = ContextT Identity

runContext :: Context a -> SourceCtx -> (a, SourceCtx)
runContext m = runState (unContextT m)

runContextT :: ContextT m a -> SourceCtx -> m (a, SourceCtx)
runContextT m = runStateT (unContextT m)

getNode :: (Monad m, HasRef a) => TypedRef a -> ContextT m a
getNode r = getsContext (lookupRef r)

putNode :: (Monad m, HasRef a) => TypedRef a -> a -> ContextT m ()
putNode r n = modifyContext (updateRef r n)

updateNode :: (HasRef a, Monad m) => (a -> a) -> TypedRef a -> ContextT m ()
updateNode f r = modifyContext (\c -> updateRef r (f (lookupRef r c)) c)

-- | Generate a completely fresh node. Note: this may violate some internal
-- invariants, so be careful.
createNode :: (HasRef a, Monad m) => a -> ContextT m (TypedRef a)
createNode a = do
  r <- unsafeCastTypedRef <$> ContextT (state sourceCtxFreshRef)
  modifyContext (updateRef r a)
  pure r

copyNode :: (Monad m, HasRef a) => TypedRef a -> ContextT m (TypedRef a)
copyNode r = do
  r' <- ContextT $ state sourceCtxFreshRef
  loc <- getsContext (\ctx -> srcCtx_locs ctx `hmUnsafeLookup` (asNodeRef r))
  node <- getNode r
  let tr' = unsafeCastTypedRef r'
  putNode tr' node
  ctx <- getsContext (\c -> c{srcCtx_locs = HashMap.insert r' loc (srcCtx_locs c)})
  let copyInfo c =
        let nodeM = HashMap.lookup (asNodeRef r) (srcCtx_nodes c)
            typeM = HashMap.lookup (unsafeCastTypedRef (asNodeRef r)) (srcCtx_exprTypes c)
            ins f k m = maybe (f c) (\v -> HashMap.insert k v (f c)) m
        in
          c{ srcCtx_nodes = ins srcCtx_nodes r' nodeM
           , srcCtx_exprTypes = ins srcCtx_exprTypes (unsafeCastTypedRef r') typeM}
  putContext (copyInfo ctx)
  pure tr'

type VdMap = HashMap VarDeclRef VarDeclRef

deepCopyExpr :: Monad m => ExprRef -> ContextT m ExprRef
deepCopyExpr r = evalStateT (doDeepCopyExpr r) HashMap.empty

doDeepCopyExpr :: Monad m => ExprRef -> StateT VdMap (ContextT m) ExprRef
doDeepCopyExpr r = do
  r' <- lift $ copyNode r
  newExpr <- lift (getsContext (lookupRef r')) >>= \case
    SolExprAssign op e1 e2 ty -> SolExprAssign op <$> doDeepCopyExpr e1 <*> doDeepCopyExpr e2 <*> pure ty
    SolExprUnaryOp op e1 -> SolExprUnaryOp op <$> doDeepCopyExpr e1
    SolExprBinaryOp op e1 e2 ty ->
      SolExprBinaryOp op <$> doDeepCopyExpr e1 <*> doDeepCopyExpr e2 <*> pure ty
    SolExprFunCall e eargs -> SolExprFunCall <$> doDeepCopyExpr e <*> traverse doDeepCopyExpr eargs
    SolExprTypeConvert ty e -> SolExprTypeConvert ty <$> doDeepCopyExpr e
    SolExprStructCons dr eargs -> SolExprStructCons dr <$> traverse doDeepCopyExpr eargs
    SolExprMember e m mr -> SolExprMember <$> doDeepCopyExpr e <*> pure m <*> pure mr
    SolExprIndex e1 e2 -> SolExprIndex <$> doDeepCopyExpr e1 <*> doDeepCopyExpr e2
    SolExprTuple es -> SolExprTuple <$> traverse doDeepCopyExpr es
    SolExprIdent x declRef -> do
      -- The variable decl map should only contain statement defined expressions.
      declRef' <- gets (HashMap.lookup (unsafeCastTypedRef declRef)) >>= \case
        Just newVd -> pure (asNodeRef newVd)
        Nothing -> pure declRef
      pure $ SolExprIdent x declRef'
    SolExprConditional e1 e2 e3 ->
      SolExprConditional <$> doDeepCopyExpr e1 <*> doDeepCopyExpr e2 <*> doDeepCopyExpr e3
    e -> pure e
  lift $ putNode r' newExpr
  pure r'

doDeepCopyVarDecl :: Monad m => VarDeclRef -> StateT VdMap (ContextT m) VarDeclRef
doDeepCopyVarDecl r = do
  r' <- lift $ copyNode r
  modify (HashMap.insert r r')
  newVd <- lift (getsContext (lookupRef r')) >>= \vd -> do
    value' <- traverse doDeepCopyExpr (varDecl_value vd)
    pure $ vd{varDecl_value=value'}
  lift $ putNode r' newVd
  pure r'

deepCopyStmt :: Monad m => StmtRef -> ContextT m StmtRef
deepCopyStmt r = evalStateT (doDeepCopyStmt r) HashMap.empty

doDeepCopyStmt :: Monad m => StmtRef -> StateT VdMap (ContextT m) StmtRef
doDeepCopyStmt r =  do
  r' <- lift $ copyNode r
  newStmt <- lift (getsContext (lookupRef r')) >>= \case
    SolStmtBlock stmts -> SolStmtBlock <$> traverse doDeepCopyStmt stmts
    SolStmtIf e bthen belse ->
      SolStmtIf <$> doDeepCopyExpr e <*> doDeepCopyStmt bthen <*> traverse doDeepCopyStmt belse
    SolStmtWhile e body -> SolStmtWhile <$> doDeepCopyExpr e <*> doDeepCopyStmt body
    SolStmtReturn es -> SolStmtReturn <$> traverse doDeepCopyExpr es
    SolStmtVarDecl vdRefs me -> do
      me' <- mapM doDeepCopyExpr me
      vdRefs' <- forM vdRefs $ \vr -> do
        vr' <- lift $ copyNode vr
        modify (HashMap.insert vr vr')
        vd <- lift $ getNode vr'
        value' <- traverse doDeepCopyExpr (varDecl_value vd)
        lift $ putNode vr' vd{varDecl_value=value'}
        pure vr'
      pure (SolStmtVarDecl vdRefs' me')
    SolStmtExpr e -> SolStmtExpr <$> doDeepCopyExpr e
    s -> pure s
  lift $ putNode r' newStmt
  pure r'

deepCopyCbody :: Monad m => CbodyRef -> ContextT m CbodyRef
deepCopyCbody r = evalStateT (doDeepCopyCbody r) HashMap.empty

doDeepCopyCbody :: Monad m => CbodyRef -> StateT VdMap (ContextT m) CbodyRef
doDeepCopyCbody r =  do
  r' <- lift $ copyNode r
  newCbody <- lift (getsContext (lookupRef r')) >>= \case
    CStateVar vd -> CStateVar <$> doDeepCopyVarDecl vd
    f@CFun{cfun_args=args, cfun_rets=rets, cfun_body=body, cfun_mods=mods} -> do
      args' <- traverse doDeepCopyVarDecl args
      rets' <- traverse doDeepCopyVarDecl rets
      mods' <- traverse (\(c, margs) -> (c,) <$> traverse doDeepCopyExpr margs) mods
      body' <- traverse doDeepCopyStmt body
      pure f{cfun_args=args', cfun_rets=rets', cfun_body=body', cfun_mods=mods'}
    CStruct n vds -> CStruct n <$> traverse doDeepCopyVarDecl vds
    CMod n s -> CMod n <$> doDeepCopyStmt s
    c -> pure c
  lift $ putNode r' newCbody
  pure r'

-- | Recursively transform each expression node (pre-order) in some monad context.
replaceExprM :: Monad m
             => (ExprRef -> SolExpr -> ContextT m SolExpr) -- ^ mapping function at each node
             -> ExprRef
             -> ContextT m ExprRef
replaceExprM f eref =
  -- Descend recursively first, then transform this node.
  getsContext (lookupRef eref) >>= go >>= f eref >>= wrap
  where
    wrap e = modifyContext (updateRef eref e) *> pure eref
    go = \case
      SolExprAssign op e1 e2 ty -> SolExprAssign op <$> replaceExprM f e1 <*> replaceExprM f e2 <*> pure ty
      SolExprUnaryOp op e1 -> SolExprUnaryOp op <$> replaceExprM f e1
      SolExprBinaryOp op e1 e2 ty -> SolExprBinaryOp op <$> replaceExprM f e1 <*> replaceExprM f e2 <*> pure ty
      SolExprFunCall e eargs -> SolExprFunCall <$> replaceExprM f e <*> traverse (replaceExprM f) eargs
      SolExprTypeConvert ty e -> SolExprTypeConvert ty <$> replaceExprM f e
      SolExprStructCons r eargs -> SolExprStructCons r <$> traverse (replaceExprM f) eargs
      SolExprMember e m r -> SolExprMember <$> replaceExprM f e <*> pure m <*> pure r
      SolExprIndex e1 e2 -> SolExprIndex <$> replaceExprM f e1 <*> replaceExprM f e2
      SolExprTuple es -> SolExprTuple <$> traverse (replaceExprM f) es
      SolExprConditional e1 e2 e3 ->
        SolExprConditional <$> replaceExprM f e1 <*> replaceExprM f e2 <*> replaceExprM f e3
      e -> pure e

-- | Recursively transform each statement node in some monad context.
replaceStmtM :: Monad m
             => (ExprRef -> SolExpr -> ContextT m SolExpr) -- ^ expression mapping function
             -> (StmtRef -> SolStmt -> ContextT m SolStmt) -- ^ statement mapping function
             -> StmtRef
             -> ContextT m StmtRef
replaceStmtM fe fs sref =
  -- Descend recursively first, then transform this node.
  getsContext (lookupRef sref) >>= go >>= fs sref >>= wrap
  where
    wrap s = modifyContext (updateRef sref s) *> pure sref
    go = \case
      SolStmtBlock stmts -> SolStmtBlock <$> traverse (replaceStmtM fe fs) stmts
      SolStmtIf e bthen belse ->
        SolStmtIf <$> replaceExprM fe e <*> replaceStmtM fe fs bthen <*> traverse (replaceStmtM fe fs) belse
      SolStmtWhile e body -> SolStmtWhile <$> replaceExprM fe e <*> replaceStmtM fe fs body
      SolStmtReturn es -> SolStmtReturn <$> traverse (replaceExprM fe) es
      SolStmtVarDecl vdRefs me -> SolStmtVarDecl vdRefs <$> traverse (replaceExprM fe) me
      SolStmtExpr e -> SolStmtExpr <$> replaceExprM fe e
      s -> pure s

-- * Utility functions

getFunctionSig :: ExprRef -> SourceCtx -> Maybe ([SolType], [SolType], SolMut)
getFunctionSig eref ctx =
  let mfref = case lookupRef eref ctx of
        SolExprIdent _ fref -> Just fref
        SolExprMember _ _ m -> m
        _ -> Nothing
  in
  case mfref of
    Nothing -> Nothing
    Just fref -> case tryLookupRef fref ctx of
      Just CFun{cfun_args = argRefs, cfun_rets = retRefs, cfun_mut=mut} ->
        let args = flip lookupRef ctx <$> argRefs
            rets = flip lookupRef ctx <$> retRefs in
          Just (varDecl_type <$> args, varDecl_type <$> rets, mut)
      Just (CStateVar (flip lookupRef ctx ->
                       SolVarDecl{ varDecl_vis = VisPublic, varDecl_type = ty })) ->
        -- autogenerated getter
        Just ([], [ty], MutView)
      _ -> Nothing
