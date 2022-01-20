{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
module LiquidSol.SafeMathElim (eliminateSafeMath) where

import Data.Either (partitionEithers)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader
import qualified SimpleSMT as SMT

import LiquidSol.LiquidTypes
import LiquidSol.SymEncode
import Control.Monad (forM_, foldM)
import LiquidSol.Solving.Horn
import Control.Applicative (Alternative((<|>)))
import Data.List (sort, isPrefixOf)

import LiquidSol.PrettyPrint (pretty, prettySexpr)
import qualified Data.HashSet as HashSet
import LiquidSol.LiOpts (LiOpts)
import qualified LiquidSol.LiOpts as LiOpts
import Data.Maybe (fromMaybe)
import Data.Time (getCurrentTime, UTCTime, diffUTCTime, addUTCTime)
import LiquidSol.Util.Unsafe
import Control.Monad.Extra (mapMaybeM, concatMapM)
import Data.Functor (($>))
import qualified Data.Set as Set
import Data.Set (Set)
import LiquidSol.Solving.CheckInv (splitCheckCons)
import LiquidSol.Solving.Templates (guessContractInv)
import Data.Bitraversable (bitraverse)
import LiquidSol.Syntax (Pred(..), Loc(..), predAndMany)
import qualified Data.Text as Text
import Data.Text (Text)

data ElimState = ElimState
  { es_opts :: LiOpts
  , es_startTime :: UTCTime -- ^ start time
  , es_gEnv :: LiGlobalEnv
  , es_delta :: Delta ()
  , es_jSafeMath :: [(Judgment LIPred, Int)]
  , es_jRest :: [Judgment LIPred]
  , es_infPreds :: Map Int InfPred
  , es_cinvName :: String
  }
  deriving (Show)

newtype ElimT m a = ElimT { runElimT :: ReaderT ElimState m a }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)
  deriving (MonadReader ElimState) via (ReaderT ElimState m)

evalElimT :: ElimT m a -> ElimState -> m a
evalElimT m es = flip runReaderT es . runElimT $ m

eliminateSafeMath
  :: MonadIO m
  => LiOpts
  -> LiGlobalEnv -> Delta () -> [LiJudgment] -> Map Int InfPred -> m (Maybe (SMT.SExpr, [Int], [Text]))
eliminateSafeMath opts gEnv delta jdmts infPreds =
  elimSafeMath opts gEnv delta jdmts infPreds >>= \case
    Just ((InvDef _ body, safe), pnames) ->
      liftIO (putStrLn $ "safe: " <> show safe) *> liftIO (print body) *> pure (Just (body, safe, pnames))
    _ -> pure Nothing

setup :: (MonadIO m, Traversable t, MonadReader ElimState m)
      => t (Judgment LIPred)
      -> SmtEncodeT m (Map Int (HornInv, SMT.SExpr))
setup initConstraints = do
  es <- ask
  -- Generate relations for local variables
  localRels <- mkLocalVarPreds (es_infPreds es)
  clearAssertStack
  -- Generate predicate for FINAL contract invariant
  (contractInv, _, _) <- mkContractInv (es_cinvName es) (es_gEnv es)
  clearAssertStack
  let invRels = Map.fromList $ contractInv : localRels
  -- Assert initial clauses
  forM_ initConstraints $ encodeJudgment invRels
  pure invRels

checkSatReadInv :: MonadIO m => String -> SmtEncodeT m (Maybe InvDef)
checkSatReadInv contractInvName = do
  checkSat >>= \case
    SMT.Unsat -> do
     pure Nothing
    SMT.Unknown -> do
      reason <- liftSolver SMT.command (SMT.fun "get-info" [SMT.const ":reason-unknown"])
      liftIO (putStrLn ("Got unknown: " <> (SMT.showsSExpr reason "")))
      pure Nothing
    SMT.Sat -> Just <$> readInvariant contractInvName

elimSafeMath
  :: MonadIO m
  => LiOpts
  -> LiGlobalEnv
  -> Delta ()
  -> [LiJudgment]
  -> Map Int InfPred
  -> m (Maybe ((InvDef, [Int]), [Text]))
elimSafeMath opts gEnv delta jdmts infPreds = do
  {-
     1. Find the safe math judgments.
     2. Assert everything except the safe math judgments.
     3. Push and assert final invariant definition.
     4. For each safe math: push, assert, check-sat, get model, pop
     5. Now with the satisfiable safe math asserts, generate the "strengthened" invariant with check-sat/get-model.
     6. Pop.
     7. Repeat from step 4 until k iterations.
  -}

  -- Find the safe math
  let subtyOnly = \case
        (JSubtype{}, _) -> True
        _ -> False
  let splitSafeMath = \case
        j@(JSubtype _ _ _ (_, PropSafeMath), _) -> Right j
        (j, _) -> Left j
  let (jRest0, jSafeMath) = partitionEithers (splitSafeMath <$> (filter subtyOnly (jdmts `zip` [(0 :: Int)..])))
  let jRest = filter f jRest0
        where
          f (JSubtype _ _ _ (_, PropAssert)) = False
          f _ = True
  let contractInvName = "contractInv"

  -- Bootstrap initial contract invariant
  startTime <- liftIO getCurrentTime
  let
    es = ElimState
      { es_opts = opts
      , es_startTime = startTime
      , es_gEnv = gEnv
      , es_delta = delta
      , es_jSafeMath = jSafeMath
      , es_jRest = jRest
      , es_infPreds = infPreds
      , es_cinvName = contractInvName
      }
  liftIO $ putStrLn "Bootstrapping..."
  (!initInv, pnames) <- flip evalElimT es $ evalSmtEncodeT opts delta $ do
    liftIO $ putStrLn "Trying templates..."
    goodTemplates <- pure []
    -- goodTemplates <- guessContractInv opts gEnv delta jRest infPreds
    liftIO $ print goodTemplates
    liftIO $ putStrLn "end templates"

    resetSmtSolver opts
    (_, params, pnames) <- mkContractInv (es_cinvName es) gEnv
    clearAssertStack
    let stoTypes = globalEnvStoVarMap gEnv
    let GlobalEnv stoLocs _ = gEnv
    let lenv = LocalEnv stoTypes []
    let stoVars = [x | (_, (x, _)) <- Map.toList stoLocs]
    let call = PUnintFn (Text.pack (es_cinvName es)) (PVar <$> stoVars)
    invInf <- predEncode lenv call
    invStart <- predEncode lenv (predAndMany goodTemplates)
    clearAssertStack
    case invInf of
      SMT.List (_:args) -> do
        -- Map the generated variables to the parameter names
        let argMap = Map.fromList [(a, x) | ((x, _), SMT.Atom a) <- params `zip` args]
        let subS = \case
              SMT.Atom x -> Map.findWithDefault (SMT.Atom x) x argMap
              SMT.List xs -> SMT.List (subS <$> xs)
        pure (InvDef params (subS invStart), pnames)
      SMT.Atom s | s == es_cinvName es -> pure (InvDef [] (SMT.bool True), pnames)
      r -> error $ "could not obtain initial invariant: " <> show r

  let maxIter = 3
  result <- evalElimT (runRefinement 0 maxIter (initInv, [], Set.empty)) es
  pure (Just (result, pnames))

checkTimeout :: MonadIO m => ElimT m Bool
checkTimeout = ask >>= \es -> checkTimeout_ (LiOpts.totalTimeout (es_opts es)) (es_startTime es)

checkTimeout_ :: MonadIO m => Maybe Int -> UTCTime -> m Bool
checkTimeout_ totalTimeout startTime =
  case totalTimeout of
    Just timeout ->
      liftIO $ getCurrentTime >>= \now ->
        pure $ now >= addUTCTime (fromInteger (toInteger timeout)) startTime
    _ -> pure False

-- | Run contract invariant refinement algorithm.
runRefinement :: MonadIO m => Int -> Int -> (InvDef, [Int], Set Int) -> ElimT m (InvDef, [Int])
runRefinement k maxIter solveState@(curInv, lastSafeIndices, _)
  | k >= maxIter = pure (curInv, lastSafeIndices)
  | otherwise = do
    liftIO $ putStrLn ("Iteration " <> show k)
    ElimState{es_opts=opts, es_delta=delta} <- ask
    -- Don't guess loop invs until a contract invariant has been tried.
    loopInvs <-
      if k == 0 || True
      then pure []
      else evalSmtEncodeT opts delta (findLoopInvariants lastSafeIndices curInv pure)
    -- Now try to infer the contract invariant
    elimSafeMathIter solveState loopInvs $ \(nextInv, safeIndices, unsatIndices) -> do
      timedOut <- checkTimeout
      nSafeMath <- asks (length . es_jSafeMath)
      if | -- No stronger invariant can be synthesized with this technique.
           null safeIndices ->
           pure (nextInv, safeIndices)
         | -- If all are safe, all are unsafe, or set of safe ops has not
           -- changed (i.e. nothing we can do): halt.
           -- OR the solver has timed out
           length safeIndices == nSafeMath
           || Set.size unsatIndices == nSafeMath
           || sort safeIndices == sort lastSafeIndices
           || timedOut ->
           pure (nextInv, safeIndices)
         | -- Move on to next strengthening iteration.
           otherwise ->
           runRefinement (k + 1) maxIter (nextInv, safeIndices, unsatIndices)

readInvariant :: MonadIO m => String -> SmtEncodeT m InvDef
readInvariant name = do
  model <- liftSolver SMT.command (SMT.List [SMT.const "get-model"])
  let defns = case model of
        SMT.List (SMT.Atom "model" : ds) -> Just ds
        -- z3 >= 4.8.10 compatibility
        SMT.List ds -> Just ds
        _ -> Nothing
  case defns >>= findMap extractInv of
    Just (argList, body) -> pure (InvDef argList body)
    _ -> error $ "failed to read invariant, unexpected response from SMT solver: " <> show (prettySexpr model)
  where
    findMap _ [] = Nothing
    findMap f (x:xs) = f x <|> findMap f xs

    extractInv xs = case xs of
      SMT.List [SMT.Atom "define-fun", SMT.Atom n, SMT.List (extractArglist -> Just argList), _, body]
        | n == name ->
          Just (argList, extractBody body)
      _ -> Nothing

    extractArglist xs = case xs of
      [] -> Just []
      (SMT.List [x, ty]) : xs' -> ((x, ty) :) <$> extractArglist xs'
      _ -> Nothing

    hasBound paramSet expr = case expr of
      SMT.Atom n -> HashSet.member n paramSet
      SMT.List ns -> any (hasBound paramSet) ns

    mkParamVarSet paramList =
      let paramVars = flip fmap paramList $ \case
                (SMT.Atom n, _) -> n
                _ -> undefined
          paramVarSet = HashSet.fromList paramVars
      in
        paramVarSet

    extractBody body = case body of
      -- Z3 can return an existentially quantified model value, so extract the properties
      -- that are not existentially quantified.
      SMT.List [SMT.Atom "exists", SMT.List params, SMT.List (SMT.Atom "!" : p : _)]
        | Just paramList <- extractArglist params
        , SMT.List (SMT.Atom "and" : clauses) <- p ->
          let paramVarSet = mkParamVarSet paramList in
            SMT.andMany [c | c <- clauses, not (hasBound paramVarSet c)]
        | Just paramList <- extractArglist params
        , SMT.List [SMT.Atom "let", SMT.List binds, SMT.List (SMT.Atom "and":clauses)] <- p
        , Just bindList <- extractArglist binds ->
          let pv1 = mkParamVarSet paramList
              bindf (bs, pv) b@(sx, e) = case sx of
                SMT.Atom x -> if hasBound pv e then (bs, HashSet.insert x pv) else (b:bs, pv)
                _ -> error "could not parse existentially quantified model value"
              (reverse -> binds', pv2) = foldl bindf ([], pv1) bindList in
            SMT.fun "let" [ SMT.List [SMT.List [x, e] | (x, e) <- binds']
                          , SMT.andMany [c | c <- clauses, not (hasBound pv2 c)]]
      _ -> body

mkForall :: [SMT.SExpr] -> SMT.SExpr -> SMT.SExpr
mkForall args body = if null args then body else SMT.fun "forall" [SMT.List args, body]

mkAuxInv :: MonadIO m => InvDef -> String -> String -> String -> SmtEncodeT m ()
mkAuxInv (InvDef argList _) contractInv curInv auxInv = do
  solver <- getSolver
  let sArgList = [SMT.List [x, s] | (x, s) <- argList]
      sArgVars = fst <$> argList
  _ <- liftIO $ SMT.declareFun solver auxInv (snd <$> argList) SMT.tBool
  let sCurInv = SMT.fun curInv sArgVars
      sAuxInv = SMT.fun auxInv sArgVars
      sContractInv = SMT.fun contractInv sArgVars
  liftIO $ do
    -- curInv(..) && auxInv(..) => contractInv(..)
    SMT.assert solver $
      mkForall sArgList (SMT.implies (SMT.and sCurInv sAuxInv) sContractInv)
    -- contractInv(..) => curInv(..)
    SMT.assert solver $
      mkForall sArgList (SMT.implies sContractInv sCurInv)
    -- contractInv(..) => auxInv(..)
    SMT.assert solver $
      mkForall sArgList (SMT.implies sContractInv sAuxInv)
  pure ()

extractCandidates :: SMT.SExpr -> Set SMT.SExpr
extractCandidates = \case
  s@(SMT.Atom x)
    | x `elem` ["false", "true"] -> Set.empty
    | "Map!" `isPrefixOf` x -> Set.empty
    | otherwise -> Set.singleton s
  s@(SMT.List xs)
    | (SMT.Atom lname:xs') <- xs, lname `elem` ["and", "or"] -> foldMap extractCandidates xs'
    | [SMT.Atom "let", SMT.List params, body] <- xs ->
      let boundVars = Map.fromList [(x, st) | SMT.List [SMT.Atom x, st] <- params]
          subBody = \case
            SMT.Atom y -> Map.findWithDefault (SMT.Atom y) y boundVars
            SMT.List ys -> SMT.List (subBody <$> ys)
      in
        extractCandidates (subBody body)
    | containsMapConst s -> Set.empty
    | otherwise -> Set.singleton s
  where
    containsMapConst = \case
      SMT.Atom x
        | "Map!" `isPrefixOf` x -> True
        | otherwise -> False
      SMT.List xs -> any containsMapConst xs

findLoopInvariants :: (MonadIO m, MonadReader ElimState m)
                   => [Int]
                   -> InvDef -- ^ current contract invariant
                   -> ([(Int, InvDef)] -> SmtEncodeT m a)
                   -> SmtEncodeT m a
findLoopInvariants safeIndices cinv cont = do
  es <- ask
  -- Remove all non-constructor contract invariant checks
  let jNoCinvs = filter f (es_jRest es)
        where f = \case
                JSubtype _ _ _ (_, PropContractInv False) -> False
                _ -> True
  let loopInvs = [i | (i, InfPred _ _ InfPredLoop) <- Map.toList (es_infPreds es)]

  -- Find candidate loop invariants
  liftIO $ putStrLn "loops"
  let failedJ = [j | (j, i) <- es_jSafeMath es, Set.notMember i (Set.fromList safeIndices)]
  loops <- if null loopInvs then pure [] else flip concatMapM failedJ $ \j -> do
    resetSmtSolver (es_opts es)
    invRels <- setup jNoCinvs
    _ <- mkCurInv cinv "curContractInv"
    mkAuxInv cinv (es_cinvName es) "curContractInv" "auxContractInv"
    encodeJudgment invRels j

    let jSimple = \case
          JSubtype _ lhs rhs _ -> (pretty lhs, pretty rhs)
          _ -> undefined
    linvs <- checkSat >>= \case
      SMT.Sat -> do
        linvs <- forM loopInvs $ \i -> do
          let (HornInv name _, _) = invRels `unsafeLookup` i
          linv@(InvDef _ body) <- readInvariant name
          liftIO (putStrLn ("Got sat: " <> SMT.showsSExpr body "" <> ": " <> show (jSimple j)))
          pure (i, linv)
        pure [(i, InvDef p body', j) | (i, InvDef p body) <- linvs
                                     , body' <- Set.toList (extractCandidates body)
                                     , body' /= SMT.bool True]
      SMT.Unknown -> do
        reason <- liftSolver SMT.command (SMT.fun "get-info" [SMT.const ":reason-unknown"])
        liftIO (putStrLn ("Got unknown: " <> SMT.showsSExpr reason "" <> ": " <> show (jSimple j)))
        pure []
      SMT.Unsat ->
        [] <$ liftIO (putStrLn ("Unsat: " <> show (jSimple j)))
    pure linvs
  liftIO $ putStrLn "end loops"

  -- Check if candidate loop invariants are consistent with contract invariant
  -- Take the strongest conjunction of candidate invariants.
  liftIO $ putStrLn "check loop invs"
  let strengthenLoopInvs curLinvs' (i, linv@(InvDef params body), j) = do
        resetSmtSolver (es_opts es)
        invRels <- setup (es_jRest es)
        encodeJudgment invRels j

        -- Contract invariant
        solver <- getSolver
        _ <- mkCurInv cinv "curContractInv"
        _ <- mkAuxInv cinv (es_cinvName es) "curContractInv" "auxContractInv"
        liftIO $ do
          let InvDef cparams _ = cinv
              sArgs = [SMT.List [x, s] | (x, s) <- cparams]
              sCinv = SMT.fun (es_cinvName es) (fst <$> cparams)
              sCurInv = SMT.fun "curContractInv" (fst <$> cparams)
          SMT.assert solver $ mkForall sArgs (SMT.implies sCinv sCurInv)

        -- Loop invariant
        let InvDef _ body' = Map.findWithDefault (InvDef params (SMT.bool True)) i curLinvs'
        let body'' = SMT.and body body'
        _ <- mkCurInv (InvDef params body'') "candLoopInv"
        let (HornInv name _, _) = invRels `unsafeLookup` i
        liftIO $ do
          let sArgList = [SMT.List [x, s] | (x, s) <- params]
              sArgVars = fst <$> params
          -- _ <- SMT.declareFun solver "auxLoopInv" (snd <$> params) SMT.tBool
          let sActLinv = SMT.fun name sArgVars
              sCandLinv = SMT.fun "candLoopInv" sArgVars
          SMT.assert solver $ mkForall sArgList (SMT.implies sCandLinv sActLinv)
          SMT.assert solver $ mkForall sArgList (SMT.implies sActLinv sCandLinv)

        -- Check
        checkSat >>= \case
          SMT.Sat -> do
            -- InvDef _ body' <- readInvariant name
            liftIO (print $ "yes: " <> pretty i <> ": " <> prettySexpr body'')
              $> Map.insert i (InvDef params body'') curLinvs'
          SMT.Unknown -> do
            reason <- liftSolver SMT.command (SMT.fun "get-info" [SMT.const ":reason-unknown"])
            liftIO (print ("no: unknown: " <> prettySexpr reason <> ": " <> prettySexpr body))
            pure curLinvs'
          SMT.Unsat ->
            curLinvs' <$ liftIO (print ("no: unsat:" <> prettySexpr body))
  !validLoopInvs <- foldM strengthenLoopInvs Map.empty loops
  liftIO $ putStrLn "end check loop invs"
  -- liftIO $ print validLoopInvs
  -- error "todo"
  cont (Map.toList validLoopInvs)

-- | Helper function to embed the given invariant into the SMT solver context
mkCurInv :: MonadIO m => InvDef -> String -> SmtEncodeT m SMT.SExpr
mkCurInv (InvDef args body) name =
  let params = SMT.List [SMT.List [x, t] | (x, t) <- args] in
    liftSolver SMT.command $ SMT.fun "define-fun" [SMT.const name, params, SMT.tBool, body]

-- | Iteration of the safe math elimination algorithm.
elimSafeMathIter :: MonadIO m
                 => (InvDef, [Int], Set Int) -- ^ current contract invariant, safe indices, unsat indices
                 -> [(Int, InvDef)] -- ^ inferred loop invariants
                 -> ((InvDef, [Int], Set Int) -> ElimT m a) -- ^ continuation to call when done
                 -> ElimT m a
elimSafeMathIter (curInv, lastSafeIndices, lastUnsatIndices) loopInvs cont = do
  -- For each safe math operation, find an invariant to strengthen our contract
  -- invariant. We can incrementally accumulate a stronger invariant as we go
  -- (which is both an optimization AND a simplification of this procedure).
  jRest <- asks es_jRest
  contractInvName <- asks es_cinvName
  opts <- asks es_opts
  delta <- asks es_delta
  let strengthen (curInv', acc) (j, i) = do
        resetSmtSolver opts
        -- Encode soft constraints and set up contract invariant predicate
        invRels <- setup jRest
        _ <- mkCurInv curInv' "curInv"
        mkAuxInv curInv' contractInvName "curInv" "auxInv"
        solver <- getSolver
        -- Assert known loop invariants
        forM_ loopInvs $ \(li, ldef@(InvDef lparams lbody)) -> do
          liftIO . print $ "using loop invariant " <> prettySexpr lbody
          let (HornInv name _, _) = invRels `unsafeLookup` li
              sArgList = [SMT.List [x, s] | (x, s) <- lparams]
              sArgVars = fst <$> lparams
          liftIO $ do
            SMT.assert solver (mkForall sArgList (SMT.implies (SMT.fun name sArgVars) lbody))
        -- Encode the hard constraint
        encodeJudgment invRels j
        let jSimple = \case
              JSubtype _ lhs rhs _ -> (pretty lhs, pretty rhs)
              _ -> undefined
        -- Check the result
        inv <- checkSat >>= \case
          SMT.Sat ->
            Right <$> readInvariant contractInvName
          SMT.Unknown -> do
            reason <- liftSolver SMT.command (SMT.fun "get-info" [SMT.const ":reason-unknown"])
            liftIO (putStrLn ("Got unknown: " <> SMT.showsSExpr reason "" <> ": " <> show (jSimple j)))
            pure (Left SMT.Unknown)
          SMT.Unsat ->
            Left SMT.Unsat <$ liftIO (putStrLn ("Unsat: " <> show (jSimple j)))
        pure (inv, (j, inv, i) : acc)
  totalTimeout <- asks (LiOpts.totalTimeout . es_opts)
  startTime <- asks es_startTime
  let strengthenOrTimeout (inv, acc) (j, i) = do
        timedOut <- liftIO $ checkTimeout_ totalTimeout startTime
        -- Strengthen if timeout not reached yet, otherwise assume unsafe
        if timedOut
          then pure (inv, (j, Left SMT.Unknown, i) : acc)
          else do
            (invEither, acc') <- strengthen (inv, acc) (j, i)
            case invEither of
              Right inv' -> pure (inv', acc')
              _ -> pure (inv, acc')

  -- Check hard constraints one-by-one. Ignore constraints that have already
  -- been proven unsat.
  jSafeMath <- asks es_jSafeMath
  (nextInv, infInvs) <- evalSmtEncodeT opts delta $
    foldM strengthenOrTimeout (curInv, []) [(j, i) | (j, i) <- jSafeMath, i `notElem` lastUnsatIndices]

  -- Find the safe and provably unsafe constraints
  let safeInvs = [(j, inv, i) | (j, Right inv, i) <- infInvs]
  let safeIndices = [i | (_, _, i) <- safeInvs]
  let unsatIndices = Set.union lastUnsatIndices $ Set.fromList [i | (_, Left SMT.Unsat, i) <- infInvs]

  cont (nextInv, safeIndices, unsatIndices)
