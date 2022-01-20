module LiquidSol.Solidity.ControlFlow
  ( BasicBlk
  , BrInfo
  , buildCfg
  , resolveGraph
  , varDefsInCfg ) where

import Control.Monad.State.Strict
import Data.DList (DList)
import qualified Data.DList as DList
import Data.Set (Set)
import qualified Data.Set as Set
-- import Data.Text (Text)
import LiquidSol.Solidity.Syntax
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import qualified Data.List.NonEmpty as NE

data BrInfo
  = BrCond ExprRef Node Node -- ^ true branch, false branch
  | BrGoto -- ^ Unconditional branch (jump)
  deriving (Show, Eq, Ord)

type BasicBlk = ([StmtRef], BrInfo)

data CfgState = CfgState
  { stEntry :: Node
  , stExit :: Node
  , stGraph :: Gr BasicBlk ()
  , stBbLabels :: [Node]
  , stCurBlk :: Maybe (Int, DList StmtRef)
  , stPrevBlk :: Node
  , stBreaks :: [Int] -- Pending breaks to loop exit
  }
  deriving (Show)

newtype CfgM a = CfgM { runCfg :: State CfgState a }
  deriving (Functor, Applicative, Monad, MonadState CfgState)

mkCfgState :: CfgState
mkCfgState = CfgState
  { stEntry = 0
  , stExit = 1
  , stBbLabels = [2..]
  , stGraph = mkGraph [{-(0, ([], BrGoto)), -}(1, ([], BrGoto))] []
  , stBreaks = []
  , stCurBlk = Just (0, mempty)
  , stPrevBlk = 0
  }

freshLbl :: CfgM Int
freshLbl = do
  lbls <- gets stBbLabels
  modify (\st -> st{stBbLabels = tail lbls})
  pure (head lbls)

endBlock :: CfgM Node
endBlock = gets stCurBlk >>= \case
  Nothing -> gets stPrevBlk
  Just (lbl, blk) -> do
    let node = (lbl, (DList.toList blk, BrGoto))
    modify (\st -> st{ stGraph = insNode node (stGraph st)
                     , stCurBlk = Nothing
                     , stPrevBlk = lbl })
    pure lbl

updateBlkBr :: Node -> BrInfo -> CfgM ()
updateBlkBr node br = modify f
  where
    f st =
      let gr = stGraph st
          (_, _, (blk, _), _) = context gr node in
        st{stGraph = insNode (node, (blk, br)) gr}

ensureBlk :: CfgM Int
ensureBlk = gets stCurBlk >>= \case
  Just (l, _) -> pure l
  Nothing -> do
    l <- freshLbl
    modify (\st -> st{stCurBlk = Just (l, mempty)})
    pure l

ensureStmtBlk :: StmtRef -> CfgM Int
ensureStmtBlk s = do
  _ <- ensureBlk
  gets stCurBlk >>= \case
    Just (l, b) ->
      let newBlk = DList.snoc b s in
        modify (\st -> st{stCurBlk = Just (l, newBlk)}) *> pure l
    _ -> undefined

buildCfg_ :: SourceCtx -> [StmtRef] -> CfgM Int
buildCfg_ ctx funBody_ = go funBody_ >>= finishCfg
  where
    finishCfg :: (Int, Bool) -> CfgM Int
    finishCfg (lbl, True) = modify (\st -> st{stGraph = insEdge (lbl, stExit st, ()) (stGraph st)}) *> pure lbl
    finishCfg (lbl, False) = pure lbl

    go :: [StmtRef] -> CfgM (Int, Bool)
    go [] = (,True) <$> endBlock
    go (sref:blkNext) =
      case lookupRef sref ctx of
        SolStmtBlock stmts -> go (stmts <> blkNext)
        SolStmtIf condRef sThen sElse -> do
          _ <- ensureStmtBlk sref
          beforeBlk <- endBlock
          tStart <- ensureBlk
          (tEnd, contT) <- go [sThen]
          ((eStart, eEnd), contE) <- case sElse of
            Nothing -> pure ((beforeBlk, beforeBlk), True)
            Just s -> do
              start <- ensureBlk
              (end, c) <- go [s]
              pure ((start, end), c)
          afterBlk <- ensureBlk
          updateBlkBr beforeBlk (BrCond condRef tStart eStart)
          let newEdges = [(beforeBlk, tStart, ()), (beforeBlk, eStart, ())]
                <> if contT then [(tEnd, afterBlk, ())] else []
                <> if contE then [(eEnd, afterBlk, ())] else []
          modify (\st -> st{ stGraph = insEdges newEdges (stGraph st) })
          go blkNext
        SolStmtWhile condRef body -> do
          beforeBlk <- endBlock
          entryBlk <- ensureStmtBlk sref *> endBlock
          outerBreaks <- gets stBreaks
          modify (\st -> st{stBreaks = []})
          bStart <- ensureBlk
          (bEnd, contB) <- go [body]
          afterBlk <- ensureBlk
          updateBlkBr entryBlk (BrCond condRef bStart afterBlk)
          breaks <- gets stBreaks
          let newEdges = [(beforeBlk, entryBlk, ()), (entryBlk, afterBlk, ()), (entryBlk, bStart, ())]
                <> if contB then [(bEnd, entryBlk, ())] else []
                <> [(blk, afterBlk, ()) | blk <- breaks]
          modify (\st -> st{ stGraph = insEdges newEdges (stGraph st)
                           , stBreaks = outerBreaks })
          go blkNext
        SolStmtBreak -> do
          _ <- ensureStmtBlk sref
          blk <- endBlock
          st@CfgState{stBreaks = breaks} <- get
          put st{ stBreaks = blk:breaks }
          pure (blk, False)
        SolStmtReturn _ -> do
          _ <- ensureStmtBlk sref
          blk <- endBlock
          modify (\st -> st{ stGraph = insEdge (blk, stExit st, ()) (stGraph st) })
          pure (blk, False)
        _ -> ensureStmtBlk sref *> go blkNext

buildCfg :: SourceCtx -> StmtRef -> (Int, Gr BasicBlk ())
buildCfg ctx root =
  let (_, st) = runState (runCfg (buildCfg_ ctx [root])) mkCfgState in
    (stEntry st, stGraph st)

-- | Get variables assigned in each block
varDefsInCfg :: SourceCtx -> Gr BasicBlk b -> [(Node, Set VarDeclRef)]
varDefsInCfg ctx gr = getBlkDefs <$> labNodes gr
  where
    getBlkDefs (node, (stmts, brInfo)) =
      (node, mconcat (getStmtDef . flip lookupRef ctx <$> stmts) <> getBrDef brInfo)
    getBrDef = \case
      BrCond e _ _ -> getExprDef e
      BrGoto -> Set.empty
    getStmtDef = \case
      SolStmtVarDecl vd _ -> Set.fromList (NE.toList vd)
      SolStmtReturn erefs -> mconcat (getExprDef <$> erefs)
      SolStmtWhile eref _ -> getExprDef eref
      _ -> Set.empty
    getLvalueDef (flip lookupRef ctx -> expr) = case expr of
      SolExprIdent _ ref -> Set.singleton (unsafeCastTypedRef ref)
      SolExprMember e _ _ -> getLvalueDef e
      SolExprIndex e _ -> getLvalueDef e
      _ -> Set.empty
    getExprDef (flip lookupRef ctx -> expr) = case expr of
      SolExprAssign _ lhs rhs _ -> getLvalueDef lhs <> getExprDef rhs
      SolExprUnaryOp _ e -> getExprDef e
      SolExprBinaryOp _ e1 e2 _ -> getExprDef e1 <> getExprDef e2
      SolExprFunCall ef eargs -> mconcat (getExprDef <$> (ef:eargs))
      SolExprTypeConvert _ e -> getExprDef e
      SolExprStructCons _ eargs -> mconcat (getExprDef <$> eargs)
      SolExprMember e _ _ -> getExprDef e
      SolExprIndex e1 e2 -> getExprDef e1 <> getExprDef e2
      SolExprTuple es -> mconcat (getExprDef <$> es)
      _ -> Set.empty

resolveGraph :: SourceCtx -> Gr BasicBlk () -> Gr ([SolStmt], BrInfo) ()
resolveGraph ctx g = nmap (\(stmts, br) -> (flip lookupRef ctx <$> stmts, br)) g
