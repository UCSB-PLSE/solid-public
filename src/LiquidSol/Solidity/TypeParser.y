-- -*- mode: text -*-
{
{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.Solidity.TypeParser where

import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import LiquidSol.Solidity.TypeLexer (Token(..))
import LiquidSol.Solidity.Syntax
}

%monad { Either String }

%tokentype { Token }
%token
    ELEM { TElem $$ }
    string { TArrTy "string" }
    bytes { TArrTy "bytes" }
    BUILTIN { TBuiltin $$ }
    IDENT { TIdent $$ }
    NUM { TNum $$ }
    VISIBILITY { TVis }
    function { TKeyword "function" }
    pure { TKeyword "pure" }
    view { TKeyword "view" }
    returns { TKeyword "returns" }
    contract { TKeyword "contract" }
    struct { TKeyword "struct" }
    int_const { TKeyword "int_const" }
    type { TKeyword "type" }
    tuple { TKeyword "tuple" }
    mapping { TKeyword "mapping" }
    memory { TKeyword "memory" }
    storage { TKeyword "storage" }
    pointer { TKeyword "pointer" }
    ref { TKeyword "ref" }
    '(' { TSymb "(" }
    ')' { TSymb ")" }
    '[' { TSymb "[" }
    ']' { TSymb "]" }
    ',' { TSymb "," }
    '=>' { TSymb "=>" }

%name parseType SolType
%error { parseError }

%%

List(P) : {[]}
        | P List(P) { $1 : $2 }

Sep1(P, s) : P { [$1] }
           | P s Sep1(P, s) { $1 : $3}

Sep(P, s) : {[]}
          | Sep1(P, s) { $1 }

Opt(P) : { Nothing }
       | P { Just $1 }

SolType :: { SolType }
SolType
  : BUILTIN { SolTyUser (error "builtin type") $1 }
  | ElemType { $1 }
  | type '(' SolType ')' { SolTyType $3 }
  | tuple '(' Sep(SolType, ',') ')' { SolTyTuple $3 }
  | contract IDENT { SolTyUser (error $ "internal error: parsed contract type needs id replaced: " <> show $2) $2 }
  | function '(' Sep(SolType, ',') ')' Opt(VISIBILITY) Opt(FunRet) Opt(FunMod) { SolTyFun $3 (fromMaybe [] $6) }
  | MemType { $1 }

MemType :: { SolType }
MemType : MemType0 memory { $1 }
        | MemType0 storage { $1 }
        | MemType0 storage pointer { $1 }
        | MemType0 storage ref { $1 }
        | MemType0 { $1 }

MemType0 :: { SolType }
MemType0
  : ArrType { $1 }
  | mapping '(' SolType '=>' SolType ')' { SolTyMapping $3 $5 }
  | string { SolTyElem "string" }
  | bytes { SolTyArr (SolTyElem "bytes") Nothing }
  | struct IDENT { SolTyUser (error $ "internal error: parsed struct needs id replaced" <> show $2 ) $2 }

ArrType :: { SolType }
ArrType
  : SolType '[' ']' { SolTyArr $1 Nothing }
  | SolType '[' NUM ']' { SolTyArr $1 (Just $3) }

FunMod
  : pure { () }
  | view { () }

FunRet :: { [SolType] }
FunRet
  : returns '(' Sep1(SolType, ',') ')' { $3 }

ElemType :: { SolType }
ElemType
  : ELEM { SolTyElem $1 }
  | int_const NUM { SolTyLitInt }

{
parseError :: [Token] -> Either String a
parseError toks = Left $ "Parse error: " ++ show toks
}
