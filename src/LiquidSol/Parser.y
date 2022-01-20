-- -*- mode: text -*-
{
{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.Parser where

import Data.Text (Text)
import qualified Data.Text as Text
import LiquidSol.Lexer (Token(..))
import LiquidSol.Syntax
import LiquidSol.Logic
}

%tokentype { Token }
%token
    true { TTrue }
    false { TFalse }
    '{' { TSymb "{" }
    '}' { TSymb "}" }
    '(' { TSymb "(" }
    ')' { TSymb ")" }
    ']' { TSymb "]" }
    '[' { TSymb "[" }
    '|' { TSymb "|" }
    ';' { TSymb ";" }
    ',' { TSymb "," }
    -- Expressions
    '=' { TSymb "=" }
    '+' { TSymb "+" }
    '-' { TSymb "-" }
    '*' { TSymb "*" }
    '/' { TSymb "/" }
    '%' { TSymb "%" }
    '++' { TSymb "++" }
    '--' { TSymb "--" }
    '+=' { TSymb "+=" }
    '-=' { TSymb "-=" }
    '>' { TSymb ">" }
    '<' { TSymb "<" }
    '>=' { TSymb ">=" }
    '<=' { TSymb "<=" }
    ':' { TSymb ":" }
    '==' { TSymb "==" }
    '!=' { TSymb "!=" }
    '=>' { TSymb "=>" }
    '==>' { TSymb "==>" }
    '<==>' { TSymb "<==>" }
    '<:' { TSymb "<:" }
    '.' { TSymb "." }
    '||' { TSymb "||" }
    '&&' { TSymb "&&" }
    '~' { TSymb "~" }
    '!' { TSymb "!" }
    int { TBuiltinTy "int" }
    uint { TBuiltinTy "uint" }
    uint8 { TBuiltinTy "uint8" }
    uint256 { TBuiltinTy "uint256" }
    address { TBuiltinTy "address" }
    bool { TBuiltinTy "bool" }
    mapping { TBuiltinTy "mapping" }
    IDENT { TIdent $$ }
    UPIDENT { TUpIdent $$ }
    INT { TInt $$ }
    -- Keywords for annotations
    typecheck { TKeyword "typecheck" }
    assume { TKeyword "assume" }
    reachable { TKeyword "assert" }
    forall { TKeyword "forall" }
    qual { TKeyword "qual" }
    reorder { TKeyword "reorder" }
    ascribe { TKeyword "ascribe" }
    sum { TKeyword "sum" }
    nnz { TKeyword "nnz" }
    flatten { TKeyword "flatten" }
    fld { TKeyword "fld" }
    sumTo { TKeyword "sumTo" }

%name parsePred Expr
%name parseAnnot Annot
%error { parseError }

%right '==>' '<==>'
%right '&&' '||'
%right '=>'
%left '==' '!='
%nonassoc '>' '<' '<=' '>='
%left '+' '-'
%left '*'
%right '~'
%nonassoc PHIGH
%nonassoc PMID
%nonassoc PLOW
%left ELOW
%left FIELD
%left LValue

%%

-- "Helper" productions
List(P) : {[]}
        | P List(P) { $1 : $2 }

Sep0(P, s) : {[]}
           | P s Sep0(P, s) { $1 : $3 }

Sep1(P, s) : P { [$1] }
           | P s Sep1(P, s) { $1 : $3}

Opt(P) : { Nothing }
       | P { Just $1 }

ANYIDENT :: { Text }
ANYIDENT : IDENT { $1 }
         | UPIDENT { $1 }

-- Grammar based on https://solidity.readthedocs.io/en/v0.6.4/miscellaneous.html#language-grammar

-- Expressions
Arith2 :: { Arith2 }
Arith2 : '+' { AAdd }
       | '-' { ASub }
       | '*' { AMul }
       | '/' { ADiv }
       | '%' { AMod }

Rel :: { Rel }
Rel : '>' { RelGt }
    | '<' { RelLt }
    | '>=' { RelGte }
    | '<=' { RelLte }
    | '!=' { RelNeq }
    | '==' { RelEq }

IntLit :: { Constant }
IntLit : INT { CInt $1 }
       | '-' INT { CInt (negate $2) }

Literal :: { Pred }
Literal : IntLit { PConst $1 }
        | true { PTrue }
        | false { PFalse }

Atom :: { Pred }
Atom
  : ANYIDENT %prec ELOW { PVar $1 }
  | Literal { $1 }
  | '(' Expr ')' { $2 }
  | sum '(' Expr ')' { PUnintFn "sum" [$3] }
  | nnz '(' Expr ')' { PUnintFn "nnz" [$3] }
  | flatten '(' Expr ')' { PUnintFn "flatten" [$3] }
  | fld '(' ANYIDENT ',' ANYIDENT ',' Expr ')' { PUnintFn "fld" [PVar $3, PVar $5, $7] }
  | Atom '.' ANYIDENT %prec FIELD { PField $1 $3 }
  | Atom '[' Expr ']' %prec PLOW { PMapInd $1 $3 }
  | '!' Atom { PNot $2 }

Term :: { Pred }
Term
  : Term Arith2 Term { PArith2 $2 $1 $3 }
  | Atom { $1 }

RelExpr :: { Pred }
RelExpr : Term Rel Term %prec PMID { PRel $2 $1 $3 }
        | Term %prec PLOW { $1 }

BoolExpr :: { Pred }
BoolExpr
  : BoolExpr '&&' BoolExpr { PAnd $1 $3 }
  | BoolExpr '||' BoolExpr { POr $1 $3 }
  | RelExpr %prec PLOW { $1 }

Expr :: { Pred }
Expr
  : BoolExpr '==>' Expr %prec PHIGH { PImplies $1 $3 }
  | BoolExpr '<==>' Expr %prec PHIGH { PIff $1 $3 }
  | BoolExpr %prec PLOW { $1 }

-- * Types
SimpleType :: { Skel () }
SimpleType
  : int { TyInt (Just 256) }
  | uint { TyInt (Just 256) }
  | uint8 { TyInt (Just 8) }
  | uint256 { TyInt (Just 256) }
  | address { TyInt (Just 160) }
  | bool {TyBool}
  | UPIDENT { TyStruct $1 [] }

ComplexType :: { Skel () }
ComplexType
  : SimpleType { $1 }
  | mapping '(' ComplexType '=>' ComplexType ')' { TyMapping $3 $5 }
  | SimpleType '[' Opt(INT) ']' { TyArray $1 $3 }

TypeName :: { RType () }
TypeName : ComplexType { RType "v" $1 () }

-- Refinement types

RType :: { RType Pred }
RType : '{' IDENT ':' ComplexType '|' Expr '}' { RType $2 (fmap (const PTrue) $4) $6 }

Annot :: { Annot }
Annot : typecheck IDENT ':' RType { ASubtype $2 $4 }
      | assume Expr { AAssume $2 }
      | reachable { AReachable }
      | qual ANYIDENT List(ANYIDENT) '=>' Expr { ADefQual $2 $3 $5 }
      | reorder List(IDENT) { APhiReorder $2 }
      | ascribe IDENT ':' RType { AAscribe $2 $4 }

{
parseError :: [Token] -> a
parseError toks = error $ "Parse error: " ++ show toks
}
