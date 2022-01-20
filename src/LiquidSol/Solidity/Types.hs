{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.Solidity.Types where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Text (Text)
import qualified Data.Text as Text

uintMax :: Int -> Integer
uintMax p = (2 ^ toInteger p) - 1

uint8Max, uint256Max :: Integer
uint8Max = uintMax 8
uint256Max = uintMax 256

bytesTypes :: HashMap Text Integer
bytesTypes = HashMap.fromList [("bytes" <> Text.pack (show i), i) | i <- [(1 :: Integer)..32]]

uintTypes :: HashMap Text Int
uintTypes = HashMap.fromList [("uint" <> Text.pack (show n), n)
                                 | i <- [(1 :: Int)..32], let n = i * 8]
