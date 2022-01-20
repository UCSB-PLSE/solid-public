{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.SourceMap
  ( SourceMap(..)
  , create
  , getLine
  , sourceMapFromFile ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO

import Prelude hiding (getLine)

-- * Source map

data SourceMap = SourceMap
  { sm_lines :: Map Int (Int, Int) -- ^ Map start character offset to line number, line length
  , sm_comments :: [(Int, Text)] -- ^ Comments indexed by start character offset
  }
  deriving (Show)

-- | Given the character offset, return the line number, and start and end offsets of the containing line.
getLine :: Int -> SourceMap -> (Int, Int, Int)
getLine offs sm = case Map.lookupLE offs (sm_lines sm) of
  Just (start, (num, end)) -> (num, start, end)
  Nothing -> error "source map is empty"

data CommentSt = ComNone | ComSlash Int | ComLine Int Text | ComMulti Int Text | ComMultiStar Int Text
  deriving (Show, Eq)

data ScanState = ScanState
  { st_start :: Int -- ^ current line start (char offset)
  , st_cur   :: Int -- ^ current char offset
  , st_line  :: Int -- ^ current line number
  , st_comment :: CommentSt -- ^ comment state
  , st_string :: Maybe Text -- ^ track string literal
  }

create :: Text -> SourceMap
create srcContents = scanChars srcContents emptySourceMap initScanState
  where
    emptySourceMap = SourceMap { sm_lines = Map.empty, sm_comments = [] }
    initScanState = ScanState
      { st_start = 0, st_cur = 0, st_line = 1, st_comment = ComNone, st_string = Nothing }
    terminateLine sm st =
      let sm' = sm{sm_lines = Map.insert (st_start st) (st_line st, st_cur st - st_start st) (sm_lines sm)
                  , sm_comments = case st_comment st of
                      ComLine i com | Just cmts <- addComment i com sm -> cmts
                      _ -> sm_comments sm
                  }
          st' = st{ st_start = st_cur st, st_line = st_line st + 1
                  , st_comment = case st_comment st of
                      ComLine _ _ -> ComNone
                      _ -> st_comment st
                  } in
        (sm', st')
    addComment i com sm
      | ":lsol:" `Text.isPrefixOf` com = Just $ (i, Text.drop 6 com) : sm_comments sm
      | otherwise = Nothing
    scanChars s sm st = case Text.uncons s of
      Nothing -> let (sm', _) = terminateLine sm st in sm'
      Just (c, s') ->
        let continue newSm newSt = scanChars s' newSm newSt{st_cur = st_cur newSt + 1} in
          if | c == '\n' -> uncurry continue (terminateLine sm st)
             | ComMulti i com <- st_comment st, c == '*' ->
                 continue sm st{st_comment = ComMultiStar i com}
             | ComMulti i com <- st_comment st ->
                 continue sm st{st_comment = ComMulti i (Text.snoc com c)}
             | ComMultiStar i com <- st_comment st, c == '/' ->
               let sm' = case addComment i com sm of
                     Just cmts -> sm{sm_comments=cmts}
                     Nothing -> sm
               in
                 continue sm' st{st_comment = ComNone}
             | ComMultiStar i com <- st_comment st ->
                 continue sm st{st_comment = ComMulti i (Text.snoc (Text.snoc com '*') c)}
             | ComNone <- st_comment st, c == '/' -> continue sm st{st_comment = ComSlash (st_cur st)}
             | ComSlash i <- st_comment st, c == '/' -> continue sm st{st_comment = ComLine i ""}
             | ComSlash i <- st_comment st, c == '*' -> continue sm st{st_comment = ComMulti i ""}
             | ComLine i com <- st_comment st ->
                 continue sm st{st_comment = ComLine i (Text.snoc com c)}
             | otherwise -> continue sm st

sourceMapFromFile :: String -> IO SourceMap
sourceMapFromFile p = do
  src <- TextIO.readFile p
  pure (create src)
