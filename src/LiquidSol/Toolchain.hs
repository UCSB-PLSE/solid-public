{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.Toolchain where

import Control.Applicative (liftA2)
import qualified Data.Map.Strict as Map
import Data.List (foldl')
import Data.Time.Clock
import LiquidSol.Syntax
import LiquidSol.SSA (ssaTransform)
import LiquidSol.StoreTransform (storeTransform)
import LiquidSol.ConsGen (evalConsGen, consGen)
import LiquidSol.Solve
import LiquidSol.LiquidTypes
import qualified LiquidSol.LiOpts as Opts

-- for parser
import qualified Data.Text.IO as TextIO
import qualified LiquidSol.Solidity.SolcParser as Sol
import qualified LiquidSol.Solidity.Syntax as Sol
import qualified LiquidSol.SourceMap as SourceMap
import qualified Data.ByteString.Lazy.Char8 as ByteString
import System.Exit (ExitCode(ExitSuccess))
import System.Process.ByteString.Lazy (readProcessWithExitCode)
import qualified Data.Text as Text
import qualified LiquidSol.SolToAst as SolToAst
import LiquidSol.Lexer (scanAnnotTokens)
import LiquidSol.Parser (parseAnnot)

import LiquidSol.Solidity.Inliner (copyLibraries, moveInitAssignments, inlineFunctions, resolveTypeIdents, constPartialEval,
  resolveInheritance, inlineEnums, expandForLoops, replaceSafeMath, inlineModifiers)
import LiquidSol.Solidity.Preprocess.Solc04x (removeSol04xEmit)
import LiquidSol.Solidity.Preprocess.ReifyConversions (reifyConversions)
-- import qualified Data.HashMap.Strict as HashMap
import LiquidSol.SafeMathElim (eliminateSafeMath)
import qualified SimpleSMT
import LiquidSol.Solving.CheckInv
import Data.Maybe (catMaybes)
import LiquidSol.Solidity.Preprocess.Inheritance (resolveSuper)
import Control.Monad.Extra (mapMaybeM)
import LiquidSol.SymEncode (evalSmtEncodeT, resetSmtSolver)
import Data.Text (Text)

data ToolchainOpts = ToolchainOpts
  {
  }

runSolcParser :: String -> FilePath -> IO (Either String (Sol.SolcDecoded, Sol.SourceCtx))
runSolcParser solcExe contractFile = do
  (exitCode, jsonString, stderr) <- readProcessWithExitCode solcExe ["--combined-json", "ast", contractFile] ""
  if exitCode == ExitSuccess
    then do
      sourceContents <- TextIO.readFile contractFile
      let sourceMap = SourceMap.create sourceContents
      pure $ Sol.decodeSolcOutput jsonString sourceMap
    else pure $ Left (ByteString.unpack stderr)

prepareSol :: Sol.SolSourceUnit -> Sol.SourceCtx -> (Sol.SolSourceUnit, Sol.SourceCtx)
prepareSol (Sol.SolSourceUnit crefs) ctx0 =
  let
    stages =
      [ removeSol04xEmit
      , expandForLoops
      , constPartialEval
      , resolveTypeIdents
      , reifyConversions
      , inlineModifiers
      , inlineEnums
      , replaceSafeMath
      , moveInitAssignments
      , resolveSuper
      , resolveInheritance
      , inlineFunctions
      , copyLibraries
      ]
  in
    (Sol.SolSourceUnit crefs, (foldl' (flip (.)) id stages) ctx0)

convertSolToIR :: Sol.SolContract -> Sol.SourceCtx -> Contract ()
convertSolToIR contract ctx =
  let annots = flip fmap (SourceMap.sm_comments (Sol.srcCtx_srcmap ctx)) $ \(i, cmt) ->
        let lexResult = scanAnnotTokens (Text.unpack cmt) in
        if | Right toks <- lexResult ->
               Just (i, parseAnnot toks)
           | Left msg <- lexResult -> error $ "Failed to parse annotation " <> show cmt <> ": " <> msg
           | otherwise -> Nothing
  in
  SolToAst.convertContract ctx{Sol.srcCtx_annots = [a | Just a <- annots]} contract

preprocess :: Delta () -> Contract () -> Contract ()
preprocess delta = fst . ssaTransform . storeTransform delta {-. moveStorageAsn-}

constraintGen :: Contract () -> ((Contract LIPred, LiGlobalEnv), [Judgment LIPred], Map.Map Int InfPred)
constraintGen = evalConsGen . consGen

solveConstraints
  :: Opts.LiOpts
  -> LiGlobalEnv
  -> Delta ()
  -> [Judgment LIPred]
  -> Map.Map Int InfPred
  -> IO (Either SolveErr Assignment, NominalDiffTime)
solveConstraints opts gEnv delta constraints infPreds = do
  let spCons = split constraints
  -- let liTypeVars = Set.toList (mconcat (liJudgmentFreeVars <$> spCons))
  -- let assign = Map.fromList (zip liTypeVars (repeat defaultQuals))
  startTime <- getCurrentTime
  !result <- evalSolveT (solveHorn gEnv delta spCons infPreds) opts
  !elapsed <- liftA2 diffUTCTime getCurrentTime (pure startTime)
  pure (fmap (const Map.empty) result, elapsed)

findRedundantSafeMath
  :: Opts.LiOpts
  -> LiGlobalEnv
  -> Delta ()
  -> [Judgment LIPred]
  -> Map.Map Int InfPred
  -> IO (Maybe (SimpleSMT.SExpr, [(Int, Judgment LIPred)], [Int], [Text]), NominalDiffTime)
findRedundantSafeMath opts gEnv delta constraints infPreds = do
  let !spCons = split constraints
  startTime <- getCurrentTime
  let safeMathChecks = [(i, j) | (j@(JSubtype _ _ _ (_, PropSafeMath)), i) <- spCons `zip` [0..]]
  !result <- eliminateSafeMath opts gEnv delta spCons infPreds
  !elapsed <- liftA2 diffUTCTime getCurrentTime (pure startTime)
  pure (fmap (\(inv, safe, pnames) -> (inv, safeMathChecks, safe, pnames)) result, elapsed)

checkInvariant
  :: Opts.LiOpts
  -> LiGlobalEnv
  -> Delta ()
  -> [Judgment LIPred]
  -> Map.Map Int InfPred
  -> Contract a
  -> Pred
  -> IO [(Judgment LIPred, Bool)]
checkInvariant opts gEnv delta constraints infPreds contract inv = do
  let storageVars = Map.fromList . catMaybes $
        let Contract _ decls = contract in
          flip fmap decls $ \case
            DVar x _ _ (Loc loc) -> Just (x, loc)
            _ -> Nothing
  let (subTyCons, pathCons) = splitCheckCons (split constraints)
  !spCons <- evalSmtEncodeT opts delta $ flip mapMaybeM subTyCons $ \case
        j@(JSubtype _ _ _ (_, _p)) -> do
          resetSmtSolver opts
          -- liftIO $ putStrLn ("check" <> show p)
          Just . (j,) <$> checkInv gEnv (j:pathCons) infPreds storageVars inv
        _ -> pure Nothing
  pure spCons
