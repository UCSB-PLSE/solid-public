{-# LANGUAGE OverloadedStrings, DeriveAnyClass #-}
module LiquidSol.SrcLoc where

import Data.Aeson (FromJSON(..))
import qualified Data.Aeson.Types as Aeson
import Data.Text (Text)
import qualified Data.Text as Text
import Text.Read.Extra (readEither)
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)

data SrcLoc = SrcLoc { srcLoc_offs :: Int, srcLoc_len :: Int }
  deriving (Show, Eq, Ord, Generic, NFData)

noSrcLoc :: SrcLoc
noSrcLoc = SrcLoc{srcLoc_offs=0, srcLoc_len=0}

readSrcLoc :: Text -> Aeson.Parser SrcLoc
readSrcLoc s = case Text.splitOn ":" s of
  [sOffs, sLen, _] | Right offs <- readEither (Text.unpack sOffs)
                   , Right slen <- readEither (Text.unpack sLen) ->
                     pure $ SrcLoc offs slen
  _ -> fail $ "bad format for srcloc: " <> Text.unpack s

instance FromJSON SrcLoc where
  parseJSON = Aeson.withText "SrcLoc" readSrcLoc
