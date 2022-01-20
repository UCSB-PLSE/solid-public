-- -*- mode: text -*-
{
{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.Solidity.TypeLexer (Token(..), scanTokens) where

import Data.Text (Text)
import Data.Text.Prettyprint.Doc (pretty, (<+>))

import qualified Data.Text as Text
import qualified Data.Text.Read as Text
}

%wrapper "monad"

$space = [\ \t]
$digit = 0-9
@ident = [A-Za-z_][a-zA-Z_ \.$digit]*
$symbol_char = [ \{ \} \( \) \; \, > \< \[ \] \| : \. ]
@keyword = function | view | pure | returns | contract | int_const | struct | type
         | mapping | tuple | memory | storage | pointer | ref
@visibility = private | public | internal | external
@builtin_ty = msg | abi | block
@elemty = uint8 | uint16 | uint24 | uint32 | uint40 | uint48 | uint56
        | uint64 | uint72 | uint80 | uint88 | uint96 | uint104
        | uint112 | uint120 | uint128 | uint136 | uint144 | uint152
        | uint160 | uint168 | uint176 | uint184 | uint192 | uint200
        | uint208 | uint216 | uint224 | uint232 | uint240 | uint248 | uint256
        | int8 | int16 | int24 | int32 | int40 | int48 | int56 | int64
        | int72 | int80 | int88 | int96 | int104 | int112 | int120 | int128
        | int136 | int144 | int152 | int160 | int168 | int176 | int184 | int192
        | int200 | int208 | int216 | int224 | int232 | int240 | int248 | int256
        | bytes[1-9] | bytes1[0-9] | bytes2[0-9] | bytes3[0-2]
        | bool | address
@arrty = string | bytes

tokens :-
    $white+ ;
    @keyword {mkL TKeyword}
    @visibility {mkL (const TVis)}
    "address payable" {mkL TElem}
    @builtin_ty {mkL TBuiltin}
    @elemty {mkL TElem}
    @arrty {mkL TArrTy}
    "=>" {mkL TSymb}
    @ident {mkL TIdent}
    $digit+ {mkLME (fmap (TNum . fst) . Text.decimal)}
    $symbol_char {mkL TSymb}
    . {lexerError}

{
data Token
  = TIdent Text
  | TSymb Text
  | TBuiltin Text
  | TElem Text
  | TArrTy Text
  | TKeyword Text
  | TVis
  | TNum Integer
  | TEof
  deriving (Show, Eq, Ord)

alexEOF :: Alex Token
alexEOF = pure TEof

mkL :: (Text -> a) -> AlexAction a
mkL f = token (\(_, _, _, input) len -> f (Text.pack (take len input)))

mkLME :: (Text -> Either b a) -> AlexAction a
mkLME f ain@(_, _, _, input) len = case f (Text.pack (take len input)) of
  Left _ -> lexerError ain len
  Right a -> pure a

lexerError :: AlexInput -> Int -> Alex a
lexerError (AlexPn _ lineNum colNum, _, _, _) _ = alexError (show pp)
  where
    pp = "lexical error at line" <+> pretty lineNum <+> "col" <+> pretty colNum

scanTokens s = runAlex s (alexSetStartCode 0 >> go)
  where
    go = do
      tok <- alexMonadScan
      if tok == TEof
        then pure []
        else (tok : ) <$> go
}
