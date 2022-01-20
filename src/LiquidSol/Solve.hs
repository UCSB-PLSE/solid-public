{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
module LiquidSol.Solve
  ( Assignment, prettyPrintAssign
  , SolveErr, prettySolveErr, SolveT(..), evalSolveT
  , assignSkel, assignEnv, assignJudg
  -- , weaken, solve, split, qualInst
  , split
  , solveHorn )
  where

-- import Debug.Trace
import Data.Maybe (isJust, mapMaybe)
import Data.Either (isRight)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc (Doc)
import Data.List (partition)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
-- import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad (filterM, join)
import Control.Monad.Extra (ifM, whenM)
import Control.Monad.Except
import Control.Monad.IO.Class ()
import qualified SimpleSMT as SMT

import LiquidSol.AstAnalysis (allVarsDecl)
import LiquidSol.Syntax
import LiquidSol.LiquidTypes
import LiquidSol.Logic
import LiquidSol.SymEncode
import LiquidSol.ConsCheck
import qualified LiquidSol.Typecheck as TC
import LiquidSol.PrettyPrint
import qualified LiquidSol.LiOpts as Opts
import System.IO.Unsafe (unsafePerformIO)
import Control.Exception (ErrorCall, catch)
import LiquidSol.Util.Unsafe
-- import qualified LiquidSol.Util.Stream as Stream
import Control.DeepSeq (NFData, deepseq)
import LiquidSol.Solving.Horn

data SolveErr
  = SENoReason
  | SEJudgment LiJudgment
  deriving (Show)

prettySolveErr :: SolveErr -> Doc ann
prettySolveErr = \case
  SENoReason -> "Internal error"
  SEJudgment j -> "Could not weaken constraint: " <> pretty j

newtype SolveT m a = SolveT { runSolveT :: Opts.OptsT (ExceptT SolveErr m) a }
  deriving ( Functor, Applicative, Monad
           , MonadError SolveErr, MonadIO, Opts.MonadOpts)

instance MonadTrans SolveT where
  lift = SolveT . lift . lift

evalSolveT :: SolveT m a -> Opts.LiOpts -> m (Either SolveErr a)
evalSolveT m opts = runExceptT . Opts.runOptsT opts . runSolveT $ m

liftMaybe :: MonadError SolveErr m => Maybe a -> m a
liftMaybe = \case
  Just a -> pure a
  Nothing -> throwError SENoReason

getAssignEncode :: MonadIO m
                => Int -> PendingSub -> Text -> LiLocalEnv -> Assignment -> SmtEncodeT m SMT.SExpr
getAssignEncode i subs v env assign = do
  let quals = assign `unsafeLookup` i
  smtQuals <- traverse (predEncode env . predSubstMany (psubVars subs) . qualToPred (PVar v)) quals
  pure (SMT.andMany smtQuals)

logSolve :: MonadIO m => Doc ann -> SolveT m ()
logSolve msg = whenM (Opts.logSolve <$> Opts.getOpts) (liftIO $ print msg)

{-
typecheckQual :: Text -> USkel -> Map Text UType -> PendingSub -> Qual -> Bool
typecheckQual v ty vars subs q =
  let envExprs = encode (Map.insert v ty (Map.map rtypeSkel vars)) (predSubstMany (psubVars subs) (qualToPred (EVar v) q))
      -- TODO: global env to provide locations
      mkTcCtx env = TC.VarCtx{TC.ctxVars=env, TC.ctxDelta=deltaEmpty, TC.ctxLocs=mempty}
      result = [TC.runTyCheck (TC.typecheckExpr qexpr) (mkTcCtx env) | (env, qexpr) <- envExprs]in
    all isRight result
  where
    encode env = \case
      PTrue -> [(env, PConst (CBool True))]
      PFalse -> [(env, PConst (CBool False))]
      PNot p -> encode env p
      PAnd p1 p2 -> encode env p1 ++ encode env p2
      POr p1 p2 -> encode env p1 ++ encode env p2
      PIff p1 p2 -> encode env p1 ++ encode env p2
      PImplies p1 p2 -> encode env p1 ++ encode env p2
      PRel r e1 e2 -> [(env, ERel r e1 e2)]
      PVar x -> [(env, EVar x)]
      PForAll k t p ->
        let env' = Map.insert k t env in encode env' p
      PUnintFn{} -> error "PUnintRel not allowed in qualifier"
      PBoolExpr e -> [(env, e)]

weaken :: MonadIO m => Opts.LiOpts -> Delta () -> LiJudgment -> Assignment -> SolveT m Assignment
weaken opts delta constraint assign = case constraint of
  JTyWellForm (LocalEnv vars _) (RType v bty (LIVar i subs)) -> do
    quals <- liftMaybe $ Map.lookup i assign
    -- Convert environment to unrefined types
    let baseVars = Map.map (const () <$>) vars
    -- Remove qualifiers that are not well-typed bools
    let newQuals = filter (typecheckQual v (shape bty) baseVars subs) quals
    pure (Map.insert i newQuals assign)
  JSubtype env (RType v1 bty1 liType) (RType v2 bty2 (LIVar j jsubs)) _ | skelEq bty1 bty2 && v1 == v2 -> do
    -- v1 = v2 should technically be allowable, but for simplicity we don't allow renaming
    quals <- liftMaybe $ Map.lookup j assign
    isLogSolver <- Opts.logSolve <$> Opts.getOpts
    -- Run solver in incremental mode, since only the qualifier is changing.
    newQuals <- evalSmtEncodeT opts delta $ do
      -- Encode the environment (local variables and path condition) on the LHS
      -- of the implication
      smtGamma <- envEncode (assignEnv assign env)
      pushHead smtGamma
      -- Encode the liquid type on the LHS of the subtyping rule
      let venv = localEnvUpdateVar v1 (RType "v" bty1 (predicate PTrue)) env
      _ <- encNewVar v1 (skelToSort bty1)
      smtLhs <- case liType of
        LIVar i subs -> getAssignEncode i subs v1 venv assign
        LIForm p -> predEncode venv p
      pushHead smtLhs
      -- Find the valid qualifiers
      qs <- flip filterM quals $ \q -> withSolverScope $ do
        -- Encode the qualifier on the RHS of the implication
        smtRhs <- predEncode venv (predSubstMany (psubVars jsubs) (qualToPred (EVar v2) q))
        pushBody smtRhs

        checkSat >>= \case
          SMT.Unsat -> when isLogSolver (liftIO $ print ("rejected " <> pretty q)) >> pure False
          SMT.Sat -> pure True
          SMT.Unknown -> do
            let msg = "Warning: when weakening qualifiers for " <> pretty constraint
                    <> ", SMT solver returned unknown for " <> pretty q <> ", assuming false"
            when isLogSolver (liftIO (print msg))
            pure False
      let inferHorn = do
            when isLogSolver $ liftIO . putStrLn $
              "Qualifiers exhausted, attempting horn clause invariant inference"
            let LocalEnv (Map.keys -> vars) _ = env
            vars' <- forM vars $ \x -> do
              smtSort <- sortEncode (getVarSort env x)
              pure (x, smtSort)
            _ <- liftSolver (\solver argSorts -> SMT.declareFun solver "inv" argSorts SMT.tBool) (snd <$> vars')
            smtRhs <- predEncode venv (predSubstMany (psubVars jsubs)
                                       (PRel RelEq (EConst (CBool True))
                                       (EUnintFn "inv" (EVar . fst <$> vars'))))
            pushBody smtRhs
            checkSat >>= \case
              SMT.Sat -> do
                inv <- liftSolver SMT.getExpr (SMT.const "inv")
                when isLogSolver (liftIO $ putStrLn "found invariant")
                liftIO $ print inv
                pure []
              _ -> when isLogSolver (liftIO $ putStrLn "horn clause inference failed") >> pure []
      qs' <- if (null qs) then inferHorn else (pure qs)
      pure qs'
    pure (Map.insert j newQuals assign)
  c -> throwError (SEJudgment c)

solve :: MonadIO m => Delta () -> [LiJudgment] -> Assignment -> SolveT m Assignment
solve delta jdmts = runSolve jdmts []
  where
    -- Worklist algorithm for constraint solving
    runSolve [] _ assign = pure assign
    runSolve (cons : remaining) valid assign = do
      logSolve  $ "Checking: " <> pretty cons
      ifM (checkConstraint delta (assignJudg assign cons))
        (runSolve remaining (cons : valid) assign)
        (do logSolve $ "Weakening: " <> pretty cons
            opts <- Opts.getOpts
            assign' <- weaken opts delta cons assign
            let changed = Map.keys (Map.differenceWith
                                    (\t1 t2 -> if t1 == t2 then Nothing else Just [])
                                    assign assign')
            logSolve $ "Updated assignment: " <> prettyPrintAssign (Map.restrictKeys assign' (Set.fromList changed))
            let (valid', toQueue) = flip partition (cons : valid) $ \case
                   -- Do not requeue well-formedness constraints, since quals will only be removed.
                  JTyWellForm{} -> True
                  judg -> Set.null (liJudgmentFreeVars judg `Set.intersection` Set.fromList changed)
            runSolve (toQueue ++ remaining) valid' assign')
-}

-- TODO: This needs some rethinking.
split :: [LiJudgment] -> [LiJudgment]
split constraints = constraints >>= \case
  -- JTyWellForm env (RType _ (TyStruct _ flds) _) -> [JTyWellForm env t | (_, t) <- flds]
  -- JSubtype env (RType _ (TyStruct _ flds1) _) (RType _ (TyStruct _ flds2) _) prop ->
  --   [JSubtype env t1 t2 prop | ((_, t1), (_, t2)) <- sort flds1 `zip` sort flds2]
  -- j@(JTyWellForm env (RType _ (TyArray t1 _) _)) -> j : split [JTyWellForm env (RType "v" t1 (predicate PTrue))]
  -- j@(JTyWellForm env (RType _ (TyMapping t1 t2) _)) ->
  --   (j :) $
  --   [ JTyWellForm env (RType "v" t1 (predicate PTrue))
  --   , JTyWellForm env (RType "v" t2 (predicate PTrue)) ] >>= split . ((:[]))
  -- JTyWellForm env (RType _ (TyFunc x skel1 skel2) _) ->
  --   [ JTyWellForm env skel1
  --   , JTyWellForm (localEnvUpdateVar x skel1 env) skel2]
  -- JSubtype env (RType _ (TyFunc x1 skel1 skel2) _) (RType _ (TyFunc x2 skel3 skel4) _) prop ->
  --   if x1 == x2
  --   then
  --     [ JSubtype env skel3 skel1 prop
  --     , JSubtype (localEnvUpdateVar x2 skel3 env) skel2 skel4 prop]
  --   else
  --     error "split: function type arguments are not equal: "
  j -> [j]

{-
qualInst :: LocalEnv p -> Contract p -> [Qual]
qualInst (LocalEnv vars _) (Contract _ decls) =
  let fvEnv = Set.fromList (Map.keys vars)
      fvDecls = foldMap allVarsDecl decls
      fvAll = fvEnv <> fvDecls
      rels = [RelEq] -- [RelEq, RelGt, RelGte, RelLt, RelLte]
      exprs = [EConst (CInt 0)] -- EConst (CInt 0) : (EVar <$> Set.toList fvAll)
      qualVars e0 = [Qual "*" (PRel r e0 e) | r <- rels, e <- exprs]
      boundsP lb ub = PAnd (PRel RelLte lb (EVar "k")) (PRel RelLt (EVar "k") ub)
      arrP r e = PRel r (EMapInd (EVar "*") (EVar "k")) e
      qualMaps =
        [ Qual "*" $ PForAll "k" (TyInt Nothing) (PImplies (boundsP (EConst (CInt 0)) ub) (arrP r e))
        | ub <- EVar <$> Set.toList fvAll
        , r <- rels, e <- [EConst (CInt 0)]]
      qualExtra = join $ flip mapMaybe decls $ \case
        DAnnot (ADefQual x ys p) -> Just $
          [ Qual "*" (fromJust mp')
          | instExprs <- sequence (take (length ys) (repeat exprs))
          , let sub = Map.fromList ((x, EVar "*") : ys `zip` instExprs)
          -- TODO: Really nasty hack, fix this
          , let mp' = errorToNothing (predSubstMany sub p)
          , isJust mp'
          ]
        _ -> Nothing
  in qualVars (PVar "*") ++ qualMaps ++ qualExtra
-}

{-# NOINLINE errorToNothing #-}
errorToNothing :: NFData a => a -> Maybe a
errorToNothing a = unsafePerformIO $ catchErr (a `deepseq` pure (Just a)) (const (pure Nothing))
  where catchErr :: IO a -> (ErrorCall -> IO a) -> IO a
        catchErr = catch

-- * Horn solver stuff

-- | Solve with horn clauses only, no templates
solveHorn :: MonadIO m => LiGlobalEnv -> Delta () -> [LiJudgment] -> Map Int InfPred -> SolveT m Bool
solveHorn gEnv delta jdmts infPreds = isJust <$> solveHornInv gEnv delta jdmts infPreds

-- | Solve horn clauses for invariant
solveHornInv :: MonadIO m => LiGlobalEnv -> Delta () -> [LiJudgment] -> Map Int InfPred -> SolveT m (Maybe SMT.SExpr)
solveHornInv gEnv delta jdmts infPreds = do
  opts <- Opts.getOpts
  evalSmtEncodeT opts delta $ do
    -- Define the local variable relations and contract invariant
    localRels <- mkLocalVarPreds infPreds
    (contractInv, _, _) <- mkContractInv "contractInv" gEnv
    let invRels = Map.fromList (contractInv:localRels)

    clearAssertStack -- don't generate anything yet

    -- Encode the subtyping constraints
    forM_ jdmts $ encodeJudgment invRels
    -- Check validity
    checkSat >>= \case
      SMT.Sat -> do
        -- liftIO $ putStrLn "Inferred invariants:"
        -- invs <- liftSolver SMT.getExprs (Map.keys revInvMap)
        model <- liftSolver SMT.command (SMT.List [SMT.const "get-model"])
        {-
        let revInvMap = Map.fromList [(rel, i) | (i, (HornInv _ _, rel)) <- Map.toList invRels]
        case model of
          SMT.List (SMT.Atom "model" : exprs) ->
            let isInv (SMT.List (SMT.Atom "define-fun" : name : _))
                  | Just _ <- Map.lookup name revInvMap = True
                isInv _ = False
                invDefs = filter isInv exprs in
              liftIO $ forM_ invDefs $ \d -> putStrLn (SMT.showsSExpr d "")
          _ -> liftIO $ putStrLn ("Warning: bad model: " <> show (SMT.showsSExpr model ""))
        -}
        pure (Just model)
      SMT.Unknown -> do
        reason <- liftSolver SMT.command (SMT.List [SMT.const "get-info", SMT.const ":reason-unknown"])
        when (Opts.logSolve opts) $ liftIO (putStrLn $ "Unknown returned by SMT solver:" <> show reason)
        _ <- throwError SENoReason
        pure Nothing
      SMT.Unsat -> do
        when (Opts.logSolve opts) $ liftIO $ putStrLn "Unsat returned by SMT solver"
        -- liftIO $ putStrLn "Counterexample (TODO: pretty print):"
        -- cex <- liftSolver SMT.command (SMT.List [SMT.const "get-proof"])
        -- liftIO $ putStrLn (SMT.showsSExpr cex "")
        _ <- throwError SENoReason
        pure Nothing
