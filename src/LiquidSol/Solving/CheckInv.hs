module LiquidSol.Solving.CheckInv where

import Control.Monad.IO.Class (MonadIO(..))
import Data.Map (Map)

import LiquidSol.LiquidTypes
import LiquidSol.SymEncode
import LiquidSol.Syntax
import LiquidSol.Solving.Horn
import qualified SimpleSMT as SMT
import Control.Monad (forM_)
import qualified Data.Map as Map
import Data.Text (Text)
import Data.Bitraversable (bitraverse)
import qualified Data.Text as Text
import Data.Maybe (mapMaybe)

checkInv
  :: MonadIO m
  => LiGlobalEnv -- ^ global environment
  -> [LiJudgment] -- ^ constraints to check
  -> Map Int InfPred -- ^ refinement type variables
  -> Map Text Int -- ^ storage variable to location
  -> Pred -- ^ invariant
  -> SmtEncodeT m Bool
checkInv gEnv jdmts infPreds stoVars inv = do
  -- Generate relations for local variables
  localRels <- mkLocalVarPreds infPreds
  -- Generate predicate for contract invariant
  let contractInvName = "contractInv"
  (contractInv, _, _) <- mkContractInv contractInvName gEnv
  clearAssertStack

  -- Set contract invariant equal to provided invariant
  let stoTypes = Map.mapMaybe (flip globalEnvLookupLoc gEnv . Loc) stoVars
  let sinv = PUnintFn (Text.pack contractInvName) (Map.elems (Map.fromList [(loc, PVar x) | (x, loc) <- Map.toList stoVars]))
  let lenv = LocalEnv stoTypes []

  -- assert that contractInv <==> provided invariant
  -- encode both
  let mkInvs = do
        sinv' <- predEncode lenv sinv
        inv' <- predEncode lenv inv
        pure (sinv', inv')
  -- forward direction
  _ <- mkInvs >>= bitraverse pushHead pushBody
  applyAndClearAssertStack
  -- backwards direction
  _ <- mkInvs >>= bitraverse pushBody pushHead
  applyAndClearAssertStack

  -- Assert constraints and check validity
  forM_ jdmts $ encodeJudgment (Map.fromList (contractInv : localRels))
  checkSat >>= \case
    SMT.Sat -> pure True
    _ -> pure False

-- | Split constraint set into checkable and necessary constraints
splitCheckCons :: [Judgment LIPred] -> ([Judgment LIPred], [Judgment LIPred])
splitCheckCons constraints = (subTyCons, pathCons)
  where
    subTyCons = flip mapMaybe constraints $ \case
      j@JSubtype{} -> Just j
      _ -> Nothing
    pathCons = flip mapMaybe subTyCons $ \case
      j@(JSubtype _ _ _ (_, tag)) -> case tag of
        PropNone -> Just j
        PropFunArg -> Just j
        PropLoopInv -> Just j
        _ -> Nothing
      _ -> Nothing
