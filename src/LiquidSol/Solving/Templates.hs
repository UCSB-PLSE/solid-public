module LiquidSol.Solving.Templates where

import Control.Monad.IO.Class (MonadIO(..))
import Data.Map (Map)

import LiquidSol.LiquidTypes
import LiquidSol.SymEncode
import LiquidSol.Syntax
import LiquidSol.Solving.Horn
import qualified SimpleSMT as SMT
import Control.Monad (forM_, forM)
import qualified Data.Map as Map
import Data.Text (Text)
import Data.Bitraversable (bitraverse)
import qualified Data.Text as Text
import LiquidSol.Solving.CheckInv (checkInv, splitCheckCons)
import LiquidSol.InvGen
import Data.Functor (($>))
import Control.Monad.Extra (mapMaybeM)
import LiquidSol.LiOpts (LiOpts)

guessContractInv
  :: MonadIO m
  => LiOpts
  -> LiGlobalEnv -- ^ global environment
  -> Delta d -- ^ global definitions
  -> [LiJudgment] -- ^ constraints
  -> Map Int InfPred -- ^ refinement type variables
  -> SmtEncodeT m [Pred]
guessContractInv opts gEnv delta constraints infPreds = do
  let GlobalEnv stoLocs _ = gEnv
  let cands = genSumInvs delta (Map.fromList [(x, skelToUskel (rtypeSkel t)) | (x, t) <- Map.elems stoLocs])
  let (subTyCons, pathCons) = splitCheckCons constraints
  let cinvCons = flip filter subTyCons $ \case
        JSubtype _ _ _ (_, PropContractInv _) -> True
        _ -> False

  let varToLoc = Map.fromList [(x, l) | (Loc l, (x, _)) <- Map.toList stoLocs]
  cinv' <- flip mapMaybeM cands $ \p -> do
    resetSmtSolver opts
    ok <- checkInv gEnv (cinvCons <> pathCons) infPreds varToLoc p
    pure $ if ok then Just p else Nothing
  pure cinv'

-- guessIter = _
