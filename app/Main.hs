{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad (forM_, when)
import Data.Foldable (traverse_)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text

import LiquidSol.PrettyPrint (pretty)
import qualified Data.Text.Prettyprint.Doc as PP
import LiquidSol.Typecheck (runTyCheck, typecheckContract, varCtxEmpty)
import LiquidSol.Toolchain
import LiquidSol.Syntax (Contract(..), Decl(DVar), rtypeSkel, noSrcLoc, SrcLoc(..), Stmt, Expr)
import LiquidSol.Solve (prettySolveErr)
import LiquidSol.LiquidTypes (Judgment(..))
import LiquidSol.InvGen
import qualified LiquidSol.Cli as Cli
import qualified LiquidSol.LiOpts as LiOpts
import LiquidSol.SourceMap (SourceMap)
import qualified LiquidSol.SourceMap as SrcMap

-- solc parser hack
import qualified LiquidSol.Solidity.SolcParser as Sol
import qualified LiquidSol.Solidity.Syntax as Sol
import qualified Data.HashMap.Strict as HashMap
-- import LiquidSol.Solidity.ControlFlow (buildCfg)
-- import LiquidSol.Solidity.PrettyPrint (prettyCfg)
-- import Data.Graph.Inductive.Dot
import LiquidSol.Toolchain (findRedundantSafeMath)
import Data.Maybe (catMaybes)
import qualified SimpleSMT
import System.Exit
import System.IO (hPutStrLn, stderr)
import LiquidSol.Lexer (scanTokens)
import LiquidSol.Parser (parsePred)

main :: IO ()
main = do
  cliOpts <- Cli.readCliOptions
  runNewParser cliOpts
  where
    isOnly opts n = case Cli.only opts of
      Nothing -> True
      Just n' -> Text.pack n' == n
    runNewParser cliOpts = do
      runSolcParser (Cli.solcBin cliOpts) (Cli.sourceFile cliOpts) >>= \case
        Left err -> putStrLn err *> error "failed to parse source file"
        Right (Sol.SolcDecoded hm, ctx0)
          | [(_, srcUnit)] <- HashMap.toList hm
          , (Sol.SolSourceUnit ctrefs, ctx) <- prepareSol srcUnit ctx0 -> do
            let runCriteria c =
                  Sol.contract_full c
                  && Sol.contract_kind c == Sol.SolContractKind
                  && isOnly cliOpts (Sol.contract_name c)
            let cts = filter runCriteria $
                  catMaybes ((\c -> Sol.tryLookupRef (Sol.asNodeRef c) ctx) <$> ctrefs)
            let cts2 = if Cli.onlyLast cliOpts && not (null cts) then [last cts] else cts
            forM_ cts2 $ \contract -> do
              when (Sol.contract_full contract && Sol.contract_kind contract == Sol.SolContractKind && isOnly cliOpts (Sol.contract_name contract)) $ do
                -- putStr "Contract: "
                -- print $ Sol.contract_name contract
                -- let body = Sol.contract_body contract
                -- forM_ body $ \cbref -> case Sol.lookupRef cbref ctx of
                --   Sol.CFun{Sol.cfun_name=name, Sol.cfun_body=Just blk} -> do
                --     print name
                --     putStrLn $ showDot (prettyCfg ctx (snd (buildCfg ctx blk)))
                --   _ -> pure ()
                let ast = convertSolToIR contract ctx
                when (Cli.debugPreprocess cliOpts) $ print (pretty ast)
                print $ "Now running on " <> pretty (Sol.contract_name contract)

                case Cli.runMode cliOpts of
                  Cli.InferMode -> runSolver (Sol.srcCtx_srcmap ctx) ast cliOpts
                  Cli.CheckMode ->
                    case Cli.checkInv cliOpts of
                      Just invStr -> runChecker (Sol.srcCtx_srcmap ctx) ast invStr cliOpts
                      Nothing ->
                        hPutStrLn stderr "missing --check-inv flag" *>
                        exitFailure
                  Cli.InvCandMode -> runInvCand ast cliOpts
                when (Cli.onlyLast cliOpts) $ exitSuccess

        Right _ -> error "multiple compilation unit Solidity file not supported"


runChecker :: SourceMap -> Contract () -> String -> Cli.CliOptions -> IO ()
runChecker srcMap ast userInv cliOpts = do
  case runTyCheck (typecheckContract ast) varCtxEmpty of
    Left (err, tr) ->
      print err *>
      print (prettyTypeErrorTrace tr) *>
      exitFailure
    Right delta -> do
      toks <- case scanTokens userInv of
            Left err -> print err *> exitFailure
            Right toks -> pure toks
      let userInv' = parsePred toks
      let ssaAst = preprocess delta ast
      let ((liAst, gEnv), constraints, infPreds) = constraintGen ssaAst
      result <- checkInvariant (Cli.solverOpts cliOpts) gEnv delta constraints infPreds liAst userInv'
      if null [j | (j@JSubtype{}, False) <- result]
        then putStrLn "OK"
        else do
          putStrLn "VIOLATED"
          forM_ result $ \case
            (JSubtype _ lhs rhs (src, tag), ok) | not ok ->
              let ppCons = pretty lhs <> " ==> " <> pretty rhs in
                print ((if ok then "OK" else "ERR " <> pretty tag <> ":") PP.<+> prettyLocInfo srcMap src <> ": " <> ppCons)
            _ -> pure ()


prettyTypeErrorTrace :: [Either (Stmt ()) Expr] -> PP.Doc ann
prettyTypeErrorTrace tr = PP.vsep (either ps pe <$> tr)
  where
    ps s = "in statement " <> pretty (show s)
    pe e = "in expression " <> pretty e

prettyLocInfo :: PP.Pretty a => SourceMap -> Maybe (a, Maybe SrcLoc) -> PP.Doc ann
prettyLocInfo srcMap src = case src of
  Just (f, Nothing) -> pretty f
  Just (f, Just loc)
    | loc /= noSrcLoc ->
        let (line, _, _) = SrcMap.getLine (srcLoc_offs loc) srcMap in
          pretty f <> ": line " <> pretty line
    | otherwise -> pretty f <> ": <no line> "
  _ -> "<unknown>"

runInvCand :: Contract () -> Cli.CliOptions -> IO ()
runInvCand ast cliOpts = do
  case runTyCheck (typecheckContract ast) varCtxEmpty of
    Left (err, tr) ->
      print err *>
      print (prettyTypeErrorTrace tr) *>
      exitFailure
    Right delta -> do
      let stoVars = Map.fromList . catMaybes $
            let Contract _ decls = ast in
              flip fmap decls $ \case
                DVar x ty _ _ -> Just (x, rtypeSkel ty)
                _ -> Nothing
      -- print stoVars
      let cands = genInv stoVars delta (Cli.invCandDepth cliOpts)
      forM_ cands $ print . pretty

runSolver :: SourceMap -> Contract () -> Cli.CliOptions -> IO ()
runSolver srcMap ast cliOpts = do
  case runTyCheck (typecheckContract ast) varCtxEmpty of
    Left (err, tr) ->
      print err *>
      print (prettyTypeErrorTrace tr)
    Right delta -> do
      let ssaAst = preprocess delta ast
      when (Cli.debugPreprocess cliOpts) $ do
        putStrLn "Pre-processed AST of contract:"
        print . pretty $ ssaAst
      putStrLn ""

      let ((_liAst, gEnv), constraints, infPreds) = constraintGen ssaAst
      when (LiOpts.logSolve (Cli.solverOpts cliOpts)) $ do
        putStrLn "Constraints:"
        let filterCons = \case
              JSubtype _ lhs rhs _ -> Just (lhs, rhs)
              _ -> Nothing
        traverse_ (print . pretty) (catMaybes (filterCons <$> constraints))
        putStrLn ""
      -- when (Cli.debugPreprocess cliOpts) $ do
      --   putStrLn "AST with liquid types:"
      --   print . pretty $ liAst
      --   putStrLn ""

      elapsed <- case Cli.solverMode cliOpts of
        Cli.FastSolve -> do
          -- let defaultQuals = qualInst localEnvEmpty ssaAst
          (result, elapsed) <- solveConstraints (Cli.solverOpts cliOpts) gEnv delta constraints infPreds
          case result of
            Left err -> putStrLn $ "Solving failed: " ++ show (prettySolveErr err)
            Right _solution -> do
              putStrLn "Success!"
          pure elapsed
        Cli.IterSolve -> do
          (result, elapsed) <- findRedundantSafeMath (Cli.solverOpts cliOpts) gEnv delta constraints infPreds
          case result of
            Nothing -> putStrLn $ "Failed to prove safety of non-safe math assertions"
            Just (inv, allMathChecks, safeMathChecks, paramNames) -> do
              putStrLn $ "Total math ops: " <> show (length allMathChecks)
              putStrLn $ "Provably safe math ops: " <> show (length safeMathChecks)
              -- Replace symbolic names in SMT solver output with program variable names
              let cinv = replaceVars inv
                    where
                      paramMap = Map.fromList [("x!" <> show i, x) | (i, x) <- [(0 :: Int)..] `zip` paramNames]
                      replaceVars = \case
                        SimpleSMT.Atom x | Just x' <- Map.lookup x paramMap ->
                                           SimpleSMT.Atom (Text.unpack x')
                        SimpleSMT.Atom y -> SimpleSMT.Atom y
                        SimpleSMT.List ss -> SimpleSMT.List (replaceVars <$> ss)
              putStrLn $ "Inferred contract invariant: " <> SimpleSMT.showsSExpr cinv ""
              putStrLn $ "The following safe math checks are redundant:"
              let mathCheckMap = Map.fromList allMathChecks
              forM_ safeMathChecks $ \i ->
                if | JSubtype _ lhs rhs (src, _) <- mathCheckMap Map.! i ->
                     print (prettyLocInfo srcMap src <> ": " <> pretty lhs <> " ==> " <> pretty rhs)
                   | otherwise -> pure ()
              putStrLn $ "The following safe math checks are necessary:"
              forM_ (Map.toList (foldl (flip Map.delete) mathCheckMap safeMathChecks)) $ \(_, j) ->
                if | JSubtype _ lhs rhs (src, _) <- j ->
                     print (prettyLocInfo srcMap src <> ": " <> pretty lhs <> " ==> " <> pretty rhs)
                   | otherwise -> pure ()
          pure elapsed

      putStrLn $ "Solving time: " ++ show elapsed
      putStrLn ""
  pure ()
