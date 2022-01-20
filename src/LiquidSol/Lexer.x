-- -*- mode: text -*-
{
{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.Lexer (Token(..), scanTokens, scanAnnotTokens) where

import Data.Text (Text)
import Data.Text.Prettyprint.Doc (pretty, (<+>))

import qualified Data.Text as Text
}

%wrapper "monad"

$space = [\ \t]
$digit = 0-9
@ident = [a-z_][a-zA-Z_ $digit]*
@upident = [A-Z][a-zA-Z_ $digit]*
$symbol_char = [ \+ \- \* \{ \} \( \) \; \, > \< \[ \] \| : \. \~ ! \% = ]
@symbol = \<==> | ==> | =[= >] | \+\+ | \-\- | [! \+ \-]= | && | \|\| | [> \<]= | \<: | $symbol_char
@keyword = struct | if | else | while | for | sum | flatten | fld | nnz
@annot_keyword = typecheck | assume | reachable | forall | qual | reorder | ascribe
@builtin_types = bool | int | int256 | uint | uint8 | uint256 | address | mapping

tokens :-
    $white+ ;
    <annot> @annot_keyword {mkL TKeyword}
    sum {mkL TKeyword}
    nnz {mkL TKeyword}
    true {mkL (const TTrue)}
    false {mkL (const TFalse)}
    @keyword {mkL TKeyword}
    @symbol {mkL TSymb}
    $digit+ {mkLS (TInt . read)}
    @builtin_types {mkL TBuiltinTy}
    @ident {mkL TIdent}
    @upident {mkL TUpIdent}
    . {lexerError}

{
data Token
  = TTrue
  | TFalse
  | TKeyword Text
  | TInt Integer
  | TIdent Text
  | TBuiltinTy Text
  | TUpIdent Text
  | TSymb Text
  | TEof
  deriving (Show, Eq, Ord)

alexEOF :: Alex Token
alexEOF = pure TEof

mkL :: (Text -> a) -> AlexAction a
mkL f = token (\(_, _, _, input) len -> f (Text.pack (take len input)))

mkLS :: (String -> a) -> AlexAction a
mkLS f = token (\(_, _, _, input) len -> f (take len input))

mkLM :: (Text -> Alex a) -> AlexAction a
mkLM f (_, _, _, input) len = f (Text.pack (take len input))

lexerError :: AlexInput -> Int -> Alex a
lexerError (AlexPn _ lineNum colNum, _, _, _) _ = alexError (show pp)
  where
    pp = "lexical error at line" <+> pretty lineNum <+> "col" <+> pretty colNum

scanTokens = scanTokens_ 0
scanAnnotTokens = scanTokens_ annot

scanTokens_ sc s = runAlex s (alexSetStartCode sc >> go)
  where
    go = do
      tok <- alexMonadScan
      if tok == TEof
        then pure []
        else (tok : ) <$> go
}
