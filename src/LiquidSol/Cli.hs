{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module LiquidSol.Cli
  ( CliOptions(..)
  , cliParser, cliParserInfo
  , readCliOptions
  , SolverMode(..)
  , RunMode(..) ) where

import Options.Applicative
import LiquidSol.LiOpts

data CliOptions = CliOptions
  { sourceFile :: FilePath
  , runMode :: RunMode
  , solverOpts :: LiOpts
  , solverMode :: SolverMode
  , debugPreprocess :: Bool
  , solcBin :: String
  , checkInv :: Maybe String
  , invCandDepth :: Int
  , only :: Maybe String
  , onlyLast :: Bool
  }
  deriving (Show)

data SolverMode = FastSolve | IterSolve
  deriving (Show, Eq, Ord)

data RunMode
  = InferMode
  | CheckMode
  | InvCandMode
  deriving (Show, Eq, Ord)

cliParserInfo :: ParserInfo CliOptions
cliParserInfo = info (cliParser <**> helper) infoMod
  where
    infoMod
       = fullDesc
      <> progDesc "Prototype refinement type inference tool for Solidity"

cliParser :: Parser CliOptions
cliParser = CliOptions
  <$> strArgument (metavar "sourceFile" <> help "The smart contract source file")
  <*> runModeParser
  <*> solverOptsParser
  <*> solverModeParser
  <*> switch (long "debug-preprocess" <> help "Show contract preprocessor output")
  <*> strOption (long "solc" <> metavar "solc" <> help "The solidity compiler executable"
                 <> showDefault <> value "solc")
  <*> optional (strOption (long "check-inv" <> short 'i' <> metavar "pred"
                           <> help "Contract invariant to use with check task"))
  <*> option auto (long "invcand-depth" <> short 'd' <> metavar "NAT"
                    <> help "Depth of proposed candidate invariants (invcand task only)"
                    <> showDefault <> value (1 :: Int))
  <*> optional (strOption (long "only" <> metavar "name" <> help "Only process this contract"
                           <> showDefault))
  <*> switch (long "only-last" <> help "Only process the last contract")

solverOptsParser :: Parser LiOpts
solverOptsParser = LiOpts
  <$> switch (long "debug-solver")
  <*> switch (long "debug-smt")
  <*> switch (long "debug-quals")
  <*> optional (strOption (long "log-dir" <> help "Directory to place query logs in"))
  <*> option auto (long "query-timeout" <> help "Timeout for a single query (ms)"
                   <> showDefault <> value (1000 :: Int))
  <*> optional (option (auto @Int) (long "total-timeout" <> help "Total solver timeout (s)"))
  <*> strOption (long "z3" <> help "Z3 executable" <> showDefault <> value "z3")

solverModeParser :: Parser SolverMode
solverModeParser = option reader (long "mode" <> help "Solver mode to use with infer task (options: iter (default), fast)" <> value IterSolve)
  where
    reader = maybeReader $ \case
      "fast" -> Just FastSolve
      "iter" -> Just IterSolve
      _ -> Nothing

runModeParser :: Parser RunMode
runModeParser = option reader (long "task" <> help "Options: infer (default), check" <> value InferMode)
  where
    reader = maybeReader $ \case
      "infer" -> Just InferMode
      "check" -> Just CheckMode
      "invcand" -> Just InvCandMode
      _ -> Nothing

readCliOptions :: IO CliOptions
readCliOptions = execParser cliParserInfo
