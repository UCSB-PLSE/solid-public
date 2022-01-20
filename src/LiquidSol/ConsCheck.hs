{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.ConsCheck
    ( checkConstraint
    , checkWellForm
    , checkSubtype ) where

import Control.Monad.IO.Class
import Data.Text (Text)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified SimpleSMT as SMT

import LiquidSol.LiquidTypes
import LiquidSol.Logic
import LiquidSol.SymEncode
import LiquidSol.SortCheck
import LiquidSol.Syntax (skelEq, shape, RType(..), Pred(..), pattern PTrue)
import qualified LiquidSol.LiOpts as Opts
-- import qualified Data.Set as Set
import Control.Monad (when)

contextToSortEnv :: Delta () -> Map Text Sort -> SortEnv
contextToSortEnv delta vars =
  SortEnv { sortEnv_vars = vars
          , sortEnv_delta = delta }

typeMapToSortMap :: Map Text (RType p) -> Map Text Sort
typeMapToSortMap = Map.map (rtypeToSort . shape)

checkConstraint :: (MonadIO m, Opts.MonadOpts m) => Delta () -> Judgment Pred -> m Bool
checkConstraint delta = \case
  JTyWellForm env skel -> pure $ checkWellForm delta env skel
  JSubtype env skel1 skel2 _ -> checkSubtype delta env skel1 skel2

checkWellForm :: Delta () -> LocalEnv Pred -> RType Pred -> Bool
checkWellForm delta (LocalEnv vars _) (RType v ty p) =
  let vSort = skelToSort ty
      sortEnv = contextToSortEnv delta (Map.insert v vSort (typeMapToSortMap vars)) in
    -- TODO: check locations when we have them
    getPredSort p sortEnv == Just SortBool

checkSubtype :: (MonadIO m, Opts.MonadOpts m) => Delta () -> LocalEnv Pred -> RType Pred -> RType Pred -> m Bool
checkSubtype delta env (RType v1 bty1 p1) (RType v2 bty2 p2)
    | v1 == v2 && skelEq bty1 bty2
    = do opts <- Opts.getOpts
         let encodeCons :: MonadIO m => SmtEncodeT m (LocalEnv Pred)
             encodeCons = do
               smtEnv <- envEncode env
               _ <- encNewVar v1 (skelToSort bty1)
               let venv = localEnvUpdateVar v1 (RType "v" bty1 (predicate PTrue)) env
               smtP1 <- predEncode venv p1
               smtP2 <- predEncode venv p2
               pushHead smtEnv
               pushHead smtP1
               pushBody smtP2
               pure venv
         evalSmtEncodeT opts delta $ do
           senv <- encodeCons
           -- liftSolver SMT.assert prop
           checkSat >>= \case
             SMT.Sat -> pure True
             SMT.Unsat -> pure False
             {-
             SMT.Sat -> do
               when isLogSolver $ do
                 let LocalEnv vars _ = senv
                 let varList = Set.toList (Map.keysSet vars)
                 svars <- traverse (getVar senv) varList
                 counterexample <- liftSolver SMT.getExprs svars
                 let resolvedCe = [(x, val) | (x, (_, val)) <- varList `zip` counterexample]
                 liftIO . putStrLn $ "Counterexample: " <> show resolvedCe
               pure False
             SMT.Unsat -> pure True
             -}
             SMT.Unknown -> do
               when (Opts.logSolve opts) (liftIO $ putStrLn "Warning: solver returned unknown")
               pure False
    | otherwise = liftIO (putStrLn "checkSubtype: warning: no matching subtype form") *> pure False
