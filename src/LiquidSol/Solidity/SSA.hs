{-# LANGUAGE OverloadedStrings, FlexibleContexts, ScopedTypeVariables #-}
module LiquidSol.Solidity.SSA where

import Control.Monad.State.Strict
import Data.Functor.Identity
import Data.DList (DList)
import qualified Data.DList as DList
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
-- import qualified Data.Graph.Inductive.Query.DFS as Graph
import qualified Data.Graph.Inductive.Query.Dominators as Graph
import qualified Data.Graph.Inductive.Query.TransClos as Graph
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Set (Set)
import qualified Data.Set as Set
-- import Data.Text (Text)
-- import qualified Data.Text as Text

import LiquidSol.Solidity.Syntax
import LiquidSol.Solidity.ControlFlow
import LiquidSol.Util.Unsafe
import LiquidSol.Solidity.ContextMonad

-- * Monad setup

data RenameTable = RTable
  { renameVars :: HashMap VarDeclRef (Int, VarDeclRef) -- ^ Variable names -> instance
  , renamePhi :: HashMap Node (HashMap VarDeclRef [VarDeclRef]) -- ^ Phi nodes in every block
  , renameCtx :: SourceCtx
  , renameCfg :: Gr BasicBlk ()
  }

mkRtableEmpty :: SourceCtx -> RenameTable
mkRtableEmpty ctx = RTable
  { renameVars = mempty
  , renamePhi = mempty
  , renameCtx = ctx
  , renameCfg = empty }

newtype RenameT m a = RenameM
  { unRenameM :: StateT RenameTable m a }
  deriving (Functor, Applicative, Monad,
            MonadState RenameTable)

type Rename = RenameT Identity

runRenameT :: RenameT f a -> RenameTable -> f (a, RenameTable)
runRenameT fa ctx = flip runStateT ctx . unRenameM $ fa

runRename :: Rename a -> RenameTable -> (a, RenameTable)
runRename m = runIdentity . runRenameT m

-- * SSA + ANF transformation algorithm

computeDomTree :: Gr a b -> Node -> Gr () ()
computeDomTree gr rootNode =
  let idomAssoc = Graph.iDom gr rootNode in
    mkUGraph [0..length idomAssoc] [(i, j) | (j, i) <- idomAssoc]

-- | DF(X) = nodes Y such that X dom a predecessor of Y
computeDomFrontier :: Gr a b -> Gr () () -> HashMap Node (Set Node)
computeDomFrontier gr domTree =
  let domSet = Graph.tc domTree
      inDf y x = any (\p -> hasEdge domSet (x, p)) (pre gr y) in
    HashMap.fromList [(x, Set.fromList [y | y <- nodes gr, inDf y x]) | x <- nodes gr]

transformCfg :: Monad m => SourceCtx -> Node -> Gr BasicBlk () -> RenameT m (Gr BasicBlk ())
transformCfg ctx rootNode gr = go
  where
    go = do
       insertPhis
       modify (\st -> st{renameCtx = ctx})
       _ <- traverseDoms rootNode
       pure gr
    -- Compute the dominator tree and dominance frontier
    domTree = computeDomTree gr rootNode
    domFrontier = computeDomFrontier gr domTree
    -- Find phi node placements
    (phiPlacements, varDefsByVar, varDefsByNode) =
      let
        varDefsByNode = varDefsInCfg ctx gr
        varDefs = HashMap.fromListWith (<>)
                  [(v, Set.singleton n) | (n, vars) <- varDefsByNode, v <- Set.toList vars]
        mapToDomFront blks = mconcat (hmUnsafeLookup domFrontier <$> Set.toList blks)
        iterBlocks :: Set Node -> Set Node
        iterBlocks blks =
          let df = mapToDomFront blks in
            if df == blks then df else iterBlocks (df <> blks)
        placementsByVar = HashMap.map iterBlocks varDefs
        placementsByNode = HashMap.fromListWith (<>)
          [(n, Set.singleton v) | (v, ns) <- HashMap.toList placementsByVar, n <- Set.toList ns]
      in
        (placementsByNode, varDefs, HashMap.fromList varDefsByNode)
    -- insert phi nodes
    insertPhis = do
      modify (\st -> st{ renameVars = HashMap.mapWithKey (\vd _ -> (0, vd)) varDefsByVar
                       , renamePhi = HashMap.map (const mempty) phiPlacements
                       , renameCfg = gr })
    -- traverse dominator tree in depth-first order
    traverseDoms node = do
      let (_, _, (blk, _), _) = context gr node
      blk' <- mconcat <$> traverse transformStmt blk
      modify $ \st ->
        let curGr = renameCfg st
            (_, _, (_, brInfo), _) = context curGr node in
          st{ renameCfg = insNode (node, (DList.toList blk', brInfo)) curGr }
      -- traverse children
      varMap <- gets renameVars
      forM (suc domTree node) $ \child -> do
        -- update phi nodes of the child with the variables
        let phiVars = Set.toList (phiPlacements `hmUnsafeLookup` child)
        let getPhiLabel v = do
              (_, decl) <- gets ((\hm -> hm `hmUnsafeLookup` v) . renameVars)
              pure (v, [decl])
        phiValues <- HashMap.fromList <$> traverse getPhiLabel phiVars
        let updatePhi = Just . \case
              Just pv -> HashMap.unionWith (<>) pv phiValues
              Nothing -> phiValues
        modify (\st -> st { renamePhi = HashMap.alter updatePhi node (renamePhi st) })
        -- TODO: insert new variable declarations for the phi
        _ <- traverseDoms child
        -- "restore" original variable scope
        modify (\st->st{renameVars = varMap})

mkRename :: Monad m => VarDeclRef -> RenameT m VarDeclRef
mkRename vd = do
  ctx <- gets renameCtx
  let (vd', ctx') = runContext (copyNode vd) ctx
  modify (\st -> st{renameCtx = ctx'})
  pure vd'

transformStmt :: Monad m => StmtRef -> RenameT m (DList StmtRef)
transformStmt sref = gets (lookupRef sref . renameCtx) >>= \case
  -- SolStmtVarDecl vdr -> do
  --   SolVarDecl vd _ e <- gets (lookupRef vdr . renameCtx)
  --   stmts <- maybe (pure mempty) transformExprAnf e
  --   pure (stmts <> DList.singleton sref)
  _ -> pure (DList.singleton sref)

transformExprAnf :: Monad m => ExprRef -> RenameT m (DList StmtRef)
transformExprAnf eref = do
  gets (lookupRef eref . renameCtx) >>= \case
    SolExprAssign _op _lhs rhs _ -> do
      -- transform rhs
      _stmts1 <- transformExprAnf rhs
      -- We want every assignment to work on immutable values, e.g.
      --     x := expr       ----> x_n := expr
      --     x.f := expr     ----> x_1 := (x_0[.f := expr])
      --     x[y] := expr    ----> x_1 := (x_0[y := expr])
      --     x[y][z] := e    ----> x_1 := (x_0[y := x_0[y][z := e]])
      -- now we have to detect the lvalue on the lhs in order to properly
      -- ge
      -- transform lhs l value
      pure mempty
    _ -> pure mempty
