-- {-# LANGUAGE OverloadedStrings #-}
module LiquidSol.Solidity.Asm
  (findLocals, findAssigns) where

import Text.Regex.TDFA ((=~))
import Text.Regex.TDFA.Text ()
import Data.Text (Text)
import Data.Set (Set)
import qualified Data.Set as Set

findLocals :: Text -> Set Text
findLocals code = Set.fromList [x | [_, x] <- asmLocals]
  where
    letRegex = "let ([a-zA-Z0-9_]+) :="
    asmLocals = code =~ letRegex :: [[Text]]

findAssigns :: Text -> Set Text
findAssigns code = Set.fromList [x | [_, x] <- asmAsns]
  where
    asnRegex = "([a-zA-Z0-9_]+) :="
    asmAsns = code =~ asnRegex :: [[Text]]
