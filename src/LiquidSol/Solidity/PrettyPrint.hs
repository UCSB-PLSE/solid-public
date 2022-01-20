{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.Solidity.PrettyPrint where

import Data.Text.Prettyprint.Doc
import LiquidSol.Solidity.ControlFlow
import LiquidSol.Solidity.Syntax
import Data.Graph.Inductive.Dot
import Data.Graph.Inductive.PatriciaTree
import Text.Dot (Dot)
import qualified Data.List.NonEmpty as NE

prettyExpr :: SourceCtx -> ExprRef -> Doc ann
prettyExpr ctx eref = case lookupRef eref ctx of
  SolExprAssign op lhs rhs _ -> hsep [pp lhs, pretty op, pp rhs]
  SolExprUnaryOp op e ->
    let pe = pp e in
      if op `elem` ["++", "--"] then pe <> pretty op else pretty op <> pe
  SolExprBinaryOp op e1 e2 _ -> hsep [pp e1, pretty op, pp e2]
  SolExprFunCall ef eargs -> pp ef <> parens (hsep (pp' <$> eargs))
  SolExprTypeConvert t e -> prettyType ctx t <> parens (pp e)
  SolExprStructCons r args ->
    let name = case lookupRef r ctx of
          CStruct n _ -> n
          _ -> "(error: not pointing to struct)"
      in pretty name <> parens (hsep (punctuate "," (pp' <$> args)))
  SolExprNew t -> "new " <> prettyType ctx t
  SolExprMember e f _ -> pp e <> "." <> pretty f
  SolExprIndex e ei -> pp e <> "[" <> pp' ei <> "]"
  SolExprIdent x _ -> pretty x
  SolExprLit l -> case l of
    SolLitInt i -> pretty i
    SolLitAddr a -> pretty a
    SolLitBool b -> if b then "true" else "false"
    SolLitString s -> pretty (show s)
  SolExprElemType t -> pretty t
  SolExprTuple args -> parens (hsep (punctuate "," (pp' <$> args)))
  SolExprConditional e1 e2 e3 -> hsep [pp e1, "?", pp e2, ":", pp e3]
  where
    pp' = prettyExpr ctx
    pp r =
      let pe = pp' r
          needParens = case lookupRef r ctx of
            SolExprAssign{} -> True
            SolExprBinaryOp{} -> True
            SolExprConditional{} -> True
            SolExprNew{} -> True
            _ -> False
      in if needParens then parens pe else pe

prettyStmtBlk :: SourceCtx -> [StmtRef] -> Doc ann
prettyStmtBlk ctx stmts = "{" <> hardline <> (indent ind (vsep (prettyStmt ctx <$> stmts))) <> hardline <> "}"
  where
    ind = 4

prettyStmt :: SourceCtx -> StmtRef -> Doc ann
prettyStmt ctx sref = case lookupRef sref ctx of
  SolStmtAsm{} -> "assembly {...}"
  SolStmtBlock stmts -> prettyStmtBlk ctx stmts
  SolStmtIf e1 _ _ -> "if" <+> parens (prettyExpr ctx e1) <+> "..."
  SolStmtContinue -> "continue"
  SolStmtBreak -> "break"
  SolStmtReturn e -> "return" <+> hsep (punctuate ", " (prettyExpr ctx <$> e))
  SolStmtEmit -> "emit (...)"
  SolStmtVarDecl (NE.uncons -> (vd0, vdRest)) me ->
    case vdRest of
      Nothing ->
        let vd = lookupRef vd0 ctx in
          hsep [ prettyType ctx (varDecl_type vd)
               , pretty (varDecl_name vd)
               , maybe ("= <zero value>") (("=" <+>) . prettyExpr ctx) me]
      Just vd1 | Just e <- me ->
        let vds = vd0 : NE.toList vd1
            ppVds = [hsep [prettyType ctx (varDecl_type vd), pretty (varDecl_name vd)]
                    | vd <- flip lookupRef ctx <$> vds ]
        in
          hsep [parens (hsep (punctuate ", " ppVds)), "=", prettyExpr ctx e]
      _ -> error "impossible"
  SolStmtExpr e -> prettyExpr ctx e
  SolStmtPlaceholder -> "_"
  _ -> emptyDoc

prettyType :: SourceCtx -> SolType -> Doc ann
prettyType ctx = \case
  SolTyElem t -> pretty t
  SolTyUser _ t -> pretty t
  SolTyArr t1 msz -> prettyType ctx t1 <> brackets (maybe emptyDoc pretty msz)
  SolTyMapping t1 t2 -> "mapping(" <> prettyType ctx t1 <> " => " <> prettyType ctx t2 <> ")"
  SolTyFun args rets ->
    let mkL ts = parens (hsep (punctuate ", " (prettyType ctx <$> ts)))
        ppr = case rets of
          [] -> emptyDoc
          _ -> " returns " <> mkL rets in
    "function" <> mkL args <> ppr
  SolTyTuple ts -> "tuple" <> parens (hsep (punctuate ", " (prettyType ctx <$> ts)))
  SolTyType t -> "type" <> parens (prettyType ctx t)

prettyBlk :: SourceCtx -> BasicBlk -> Doc ann
prettyBlk ctx (stmts, _) = prettyStmtBlk ctx stmts

prettyCfg :: SourceCtx -> Gr BasicBlk () -> Dot ()
prettyCfg ctx gr = fglToDotGeneric gr (show . prettyBlk ctx) (const "") id
