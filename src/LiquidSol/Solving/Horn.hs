{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
module LiquidSol.Solving.Horn where

import Control.Monad (forM)
import Control.Monad.Extra (concatMapM, forM_)
import Control.Monad.IO.Class (MonadIO(..))
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc (pretty)
import qualified Data.Map.Strict as Map
import qualified SimpleSMT as SMT

import LiquidSol.LiquidTypes
import LiquidSol.Logic
import LiquidSol.SymEncode
import LiquidSol.Syntax
import Data.Maybe (catMaybes)
import LiquidSol.Util.Unsafe
import Data.Map (Map)
import Data.List (sort)

-- | Invariant definition, defined by arglist and body.
data InvDef = InvDef [(SMT.SExpr, SMT.SExpr)] SMT.SExpr
  deriving (Show, Eq, Ord)

getCheckedOutVars :: PendingSub -> [(Text, Loc)]
getCheckedOutVars psub = [(x, l) | (l, PVar x) <- Map.toList (psubLocs psub)]

mkLocalVarPreds :: MonadIO m
                => Map Int InfPred -> SmtEncodeT m [(Int, (HornInv, SMT.SExpr))]
mkLocalVarPreds infPreds = do
  logMessage "; Other predicates to infer"
  -- Define inferred predicates for local variables
  let mkLocalSorts name vars info = do
        -- Get sorts of arguments
        (hornInfo, argSorts) <- fmap unzip $ forM vars $ \(x, _) ->
          let srt = getVarSort (LocalEnv (Map.fromList vars) []) x in
            ((x, srt), ) <$> sortEncode srt
        -- Fetch the sorts of the auxiliary expressions of each argument
        splice <- concatMapM getAuxExpr (snd <$> hornInfo)
        funSorts <- concatMapM getUnintFunSorts (snd <$> hornInfo)
        let spliceArgSorts = fst <$> splice
        pure (HornInv name info, argSorts <> spliceArgSorts <> (snd <$> funSorts))
  -- Define the local variable relations
  localRels <- forM (Map.toList infPreds) $ \(li, info@(InfPred env inf _)) -> do
    case inf of
      Left invVars -> do
        let name = "inv_" <> show li
        (hornInv, fargs) <- mkLocalSorts name (env <> invVars) info
        invRel <- liftSolver (\slv -> SMT.declareFun slv name fargs) SMT.tBool
        pure $ Just (li, (hornInv, invRel))
      Right _ -> pure Nothing
  pure (catMaybes localRels)

-- | Inferred horn clause invariant
data HornInv = HornInv String InfPred
  deriving (Show)

mkContractInv :: (MonadIO m, Num a) => String -> GlobalEnv p -> SmtEncodeT m ((a, (HornInv, SMT.SExpr)), [(SMT.SExpr, SMT.SExpr)], [Text])
mkContractInv name gEnv = do
  let GlobalEnv globalLocs _ = gEnv
  globalVarSorts <- pure [] {- forM (solidityGlobalVars @()) $ \(_, RType _ skel _) ->
    let s = skelToSort skel in
      (s,) <$> sortEncode s -}
  stateVarSorts <- forM (Map.toList globalLocs) $ \(l, (x, RType _ skel _)) ->
    let s = skelToSort skel in
      (x, l, s,) <$> sortEncode s

  let varSorts = globalVarSorts <> [(x, s, ss) | (x, _, s, ss) <- stateVarSorts]
  -- (auxSorts, _) <- unzip <$> concatMapM getAuxExpr [s | (_, s, _) <- varSorts]
  funSorts <- concatMapM getUnintFunSorts [s | (_, s, _) <- varSorts]
  let fargs = [(x, ss) | (x, _, ss) <- varSorts] <> [(Text.pack x, ss) | (x, ss) <- funSorts]
  let paramList = [(SMT.const ("x!" <> show i), srt) | (i, srt) <- [(0 :: Int)..] `zip` (snd <$> fargs)]
  let hornInv = HornInv name (InfPred [] (Right []) InfPredOther)
  logMessage "; Contract invariant"
  sinv <- liftSolver (\slv -> SMT.declareFun slv name (snd <$> fargs)) SMT.tBool
  pure ((0, (hornInv, sinv)), paramList, fst <$> fargs)

encodeJudgment :: MonadIO m => Map Int (HornInv, SMT.SExpr) -> Judgment LIPred -> SmtEncodeT m ()
encodeJudgment hornInfo = \case
  j@(JSubtype env (RType v1 bty1 lv1) (RType v2 bty2 lv2) _) -> do
    logMessage $ "; SMT encoding for constraint " <> show (pretty j)
    -- Encode the environment (local variables and path condition) on the LHS
    -- of the implication
    smtGamma <- envEncode (assignInvEnv env)
    do
      svMap <- forM (Map.keys (localEnvVars env)) $ \x -> do
        s <- getVar_ env x
        pure (s, x)
      forM_ (sort svMap) $ \(s, x) ->
        logMessage $ "; " <> s <> " -> " <> Text.unpack x
    pushHead smtGamma
    let mkLv v bty lv = do
          let venv = localEnvUpdateVar v (RType "v" bty (predicate PTrue)) env
          let sort = skelToSort bty
          sv <- encNewVar_ v sort
          logMessage $ "; " <> sv <> " -> " <> show (pretty lv)
          cons <- case lv of
            LIVar i subs -> predEncode venv (assignLiVar env v i subs)
            LIForm p -> predEncode venv p
          pure (sv, cons)

    -- Encode the liquid types in the subtyping rule
    (sv1, smtLhs) <- mkLv v1 bty1 lv1
    pushHead smtLhs
    (sv2, smtRhs) <- mkLv v2 bty2 lv2
    -- liftIO $ print smtLhs
    -- liftIO $ print smtRhs
    -- Set LHS = RHS
    (_, auxFs) <- unzip <$> getAuxExpr (skelToSort bty1)
    auxEqs <- forM auxFs $ \f -> SMT.eq <$> (f sv1) <*> (f sv2)
    pushHead (SMT.andMany ((SMT.eq (SMT.const sv1) (SMT.const sv2)) : auxEqs))
    -- Now assert the RHS
    pushBody smtRhs
    applyAndClearAssertStack
  _ -> pure ()
  where
    assignInvSkel :: LiLocalEnv -> Skel LIPred -> Skel Pred
    assignInvSkel env = \case
      TyInt m -> TyInt m
      TyBool -> TyBool
      TyUnit -> TyUnit
      TyByte -> TyByte
      TyAddress -> TyAddress
      TyFunc n rt1 rt2 -> TyFunc n (assignInvRtype env rt1) (assignInvRtype env rt2)
      TyStruct n flds -> TyStruct n [(f, assignInvRtype env r) | (f, r) <- flds]
      TyMapping s1 s2 -> TyMapping (assignInvSkel env s1) (assignInvSkel env s2)
      TyArray s1 msz -> TyArray (assignInvSkel env s1) msz
    assignInvRtype :: LiLocalEnv -> RType LIPred -> RType Pred
    assignInvRtype env (RType v bty liVar) = case liVar of
      LIVar li psubs -> RType v (assignInvSkel env bty) (assignLiVar env v li psubs)
      LIForm p -> RType v (assignInvSkel env bty) p
    assignLiVar (LocalEnv envVars _) _ li psubs =
      -- Convert this into the uninterpreted pred generated above
      let (HornInv name (InfPred vars info _), _) = unsafeLookup hornInfo li
          storageVars = [PVar x | (x,  _) <- getCheckedOutVars psubs, Map.member x envVars]
          globalVars = [] -- [PVar x | (x, _) <- solidityGlobalVars @()]
          args = case info of
            -- Global variable
            Right _ -> globalVars <> storageVars
            -- Local variables, but with contract invariant
            Left _ | li == 0 -> globalVars <> storageVars
            -- Local variable
            Left invArgs ->
              let doSub x = unsafeLookup (psubVars psubs) x in
                (PVar . fst <$> vars) <> (doSub . fst <$> invArgs)
      in
        PUnintFn (Text.pack name) args
    assignInvEnv env@(LocalEnv vars preds) =
      LocalEnv (Map.map (assignInvRtype env) vars) preds
