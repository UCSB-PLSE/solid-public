{-# OPTIONS -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}

module LiquidSol.PrettyPrint (pretty, prettyPrintAssign, prettySexpr) where

import Data.Text.Prettyprint.Doc
import Data.Text (Text)
import qualified Data.Map.Strict as Map
import qualified SimpleSMT as SMT

import LiquidSol.Syntax
import LiquidSol.LiquidTypes
import LiquidSol.Logic (exprToPred, Sort(..))


-- * Syntax pretty printing

instance Pretty Arith2 where
  pretty = \case
    AAdd -> "+"
    ASub -> "-"
    AMul -> "*"
    ADiv -> "/"
    AMod -> "%"
    AAddMod -> "+%"

instance (Refineable a, Pretty a) => Pretty (Skel a) where
  pretty = \case
    TyInt m -> "uint" <> maybe emptyDoc pretty m
    TyBool -> "bool"
    TyUnit -> "unit"
    TyByte -> "byte"
    TyAddress -> "address"
    TyStruct name fields -> pretty name
      <> braces (hsep (punctuate "," [pretty n <+> ":" <+> pretty t | (n, t) <- fields]))
    TyFunc x t1 t2 -> pretty x <> ":" <> pretty t1 <+> "->" <+> pretty t2
    TyMapping vty kty ->
      "mapping" <> parens (pretty vty <+> "=>" <+> pretty kty)
    TyArray t msz -> pretty t <> brackets (maybe emptyDoc pretty msz)

instance Pretty Sort where
  pretty = \case
    SortInt m -> "uint" <> maybe emptyDoc pretty m
    SortBool -> "bool"
    SortByte -> "byte"
    SortArray t msz -> pretty t <> brackets (maybe emptyDoc pretty msz)
    SortMapping s1 s2 -> "mapping" <> brackets (pretty s1 <+> "," <+> pretty s2)
    SortStruct name -> "struct" <+> pretty name

instance (Refineable a, Pretty a) => Pretty (RType a) where
  pretty t@(RType _ ty a)
    | predicateIsTrue a = pretty ty
    | otherwise = prettyRtype t

prettyRtype :: (Refineable a, Pretty a) => RType a -> Doc ann
prettyRtype (RType v ty a) = braces (pretty v <> ":" <> pretty ty <+> "|" <+> pretty a)

instance Pretty Constant where
  pretty = \case
    CInt x -> pretty x
    CAddress x -> pretty x <> "{addr}"
    CBool True -> "true"
    CBool False -> "false"
    CMapZero t1 t2 -> "__mapping_zero" <> parens (pretty t1 <> ", " <> pretty t2)
    CArrZero t msz -> "__arr_zero" <> parens (pretty t <> maybe emptyDoc ((", " <>) . pretty) msz)
    CStruct name fields -> pretty name
      <+> braces (hsep (punctuate "," [pretty n <+> "=" <+> pretty c | (n, c) <- fields]))
    CByte x -> pretty x
    CString s -> pretty (show s)

instance Pretty Expr where
  pretty = pretty . exprToPred

inBlock :: Doc ann -> Doc ann
inBlock pp = surround (indent 4 pp) (lbrace <> hardline) (hardline <> rbrace)

instance Pretty Annot where
  pretty = \case
    ASubtype x ty -> hsep ["typecheck", pretty x, ":", prettyRtype ty]
    AAscribe x ty -> hsep ["ascribe", pretty x, ":", prettyRtype ty]
    AAssume p -> hsep ["assume", pretty p]
    AReachable -> "reachable"
    ADefQual x xs p -> "qual" <+> (hsep (pretty <$> (x : xs))) <+> "=>" <+> pretty p
    APhiReorder xs -> "reorder" <+> (hsep (pretty <$> xs))

instance Pretty LValue where
  pretty = \case
    LvVar x -> pretty x
    LvInd l e -> pretty l <> brackets (pretty e)
    LvFld l f -> pretty l <> "." <> pretty f

prettyPhi :: (Refineable p, Pretty p) => PhiNode p -> Doc ann
prettyPhi phi = vsep $
  punctuate ";" [hsep [pretty ty, pretty x, "="
                          , "$phi" <> parens (hsep (punctuate "," (pretty <$> pxs)))]
                | (x, ty, pxs) <- phi]

instance (Refineable p, Pretty p) => Pretty (Stmt p) where
  pretty = \case
    SDecl v ty me ->
      let base = [pretty ty, pretty v]
          rest = maybe [] (\e -> ["=", pretty e]) me
      in hsep (base ++ rest) <> ";"
    SAsn l e -> pretty l <+> "=" <+> pretty e <> ";"
    SCall asgns name args ->
      let ppasn = case asgns of
            [(x, t)] -> hsep [pretty t, pretty x, "= "]
            [] -> emptyDoc
            _ -> parens (hsep (punctuate "," [hsep [pretty t, pretty x] | (x, t) <- asgns])) <> " = "
      in ppasn <> pretty name <> parens (hsep (punctuate "," (pretty <$> args))) <> ";"
    SIf phi e b1 b2 ->
      let ppelse = if null b2
            then emptyDoc
            else " else " <> inBlock (prettyBlock b2)
          ppphi = if null phi then emptyDoc
            else " phi " <> inBlock (prettyPhi phi)
      in "if" <+> parens (pretty e) <+> inBlock (prettyBlock b1) <> ppelse <> ppphi
    SWhile phi e b2 ->
      let ppb b = inBlock (prettyBlock b) in
        "while" <+> inBlock (prettyPhi phi) <+> parens (pretty e) <+> ppb b2
    SFetch fs isDecl ->
      let ppf x ty loc = hsep [if isDecl then pretty ty else emptyDoc, pretty x, "from", pretty loc]
          fetches = vsep (punctuate ";" [ppf x ty loc | (x, ty, loc) <- fs]) in
        vsep ["fetch {", indent 4 fetches, "}"]
    SCommit cs ->
      let ppc loc e = hsep [pretty e, "to", pretty loc] in
        vsep ["commit {", indent 4 (vsep (punctuate ";" [ppc e loc | (e, loc) <- cs])), "}"]
    SAnnot ann ->
      group ("//:lsol:" <+> pretty ann)
    SReturn e ->
      "return" <+> pretty e
    SHavoc ->
      "havoc"
    SAbort ->
      "abort"

prettyBlock :: (Refineable p, Pretty p) => Block p -> Doc ann
prettyBlock b = vsep (pretty <$> blockStmts b)

instance Pretty Loc where
  pretty (Loc l) = pretty l

instance Pretty Visibility where
  pretty = \case
    VisInt -> "internal"
    VisExt -> "external"

instance Pretty Mutability where
  pretty = \case
    MutStateless -> "stateless"
    MutReadonly -> "readonly"
    MutStateful -> "readwrite"

instance (Refineable p, Pretty p) => Pretty (Decl p) where
  pretty = \case
    DVar v ty me l ->
      let base = [pretty ty, pretty v]
          rest = maybe [] (\e -> ["=", pretty e]) me
      in hsep (base ++ rest) <+> "at" <+> pretty l <> ";"
    DFun { dfun_name=name, dfun_args=args, dfun_res=res, dfun_body=body
         , dfun_vis=vis, dfun_mut=mut} ->
      prettyFun ("function" <+> pretty name) (Just mut) vis args res body
    DCtor {dctor_args=args, dctor_body=body} ->
      prettyFun "constructor" Nothing VisExt args [] body
    DStruct {dsct_name=name, dsct_fields=fields} ->
      let
        ppfld n t = pretty t <+> pretty n <> ";"
        flds = indent 4 (vsep (uncurry ppfld <$> fields))
      in
        "struct" <+> pretty name <+> "{" <> hardline <> flds <> hardline <> "}"
    DAnnot ann -> group ("//:lsol:" <+> pretty ann)
    where
      prettyFun :: Doc ann -> Maybe Mutability -> Visibility -> [(Text, RType p)] -> [(Text, RType p)] -> Block p -> Doc ann
      prettyFun descriptor mmut vis args res body =
        let params plist = hsep $ punctuate "," [pretty ty <+> pretty x | (x, ty) <- plist]
            ret = if not (null res) then ["returns", parens (params res)] else []
            ppbody = prettyBlock body
            mut = maybe [] ((:[]) . pretty) mmut in
        hsep ((descriptor <> parens (params args)) : mut <> (pretty vis : ret)) <+>
        inBlock ppbody

instance (Refineable p, Pretty p) => Pretty (Contract p) where
  pretty (Contract name body) =
    "contract" <+> pretty name <+> inBlock (vsep (pretty <$> body))

-- * Logic pretty printing

instance Pretty Rel where
  pretty = \case
    RelGt -> ">"
    RelLt -> "<"
    RelEq -> "=="
    RelNeq -> "!="
    RelLte -> "<="
    RelGte -> ">="

instance Pretty Pred where
  pretty = \case
    PConst c -> pretty c
    PVar t -> pretty t
    PRel rel e1 e2 -> pp e1 <+> pretty rel <+> pp e2
    PArith2 op e1 e2 -> pp e1 <+> pretty op <+> pp e2
    PAnd e1 e2 -> pp e1 <+> "&&" <+> pp e2
    POr e1 e2 -> pp e1 <+> "||" <+> pp e2
    PNot e1 -> "!" <> pp e1
    PImplies p1 p2 -> pp p1 <+> "==>" <+> pp p2
    PIff p1 p2 -> pp p1 <+> "<==>" <+> pp p2
    PMapInd x e -> pretty x <> brackets (pretty e)
    PMapPut x e1 e2 -> "__mapping_put" <>
      parens (hsep $ punctuate "," [pretty x, pretty e1, pretty e2])
    PField e f -> pp e <> "." <> pretty f
    PFieldUpd e f ef -> pp e <> braces (pretty f <+> ":=" <+> pretty ef)
    PUnintFn n args -> pretty n <> parens (hsep (punctuate "," (pretty <$> args)))
    PHavoc ty -> "havoc" <> brackets (pretty ty)
    PCast e ty -> "cast" <> brackets (pretty ty) <> parens (pretty e)
    where
      pp p = if isComplex p then parens (pretty p) else pretty p
      isComplex = \case
        PConst{} -> False
        PVar{} -> False
        PMapInd{} -> False
        PMapPut{} -> False
        PFieldUpd{} -> False
        PUnintFn{} -> False
        _ -> True

-- * Liquid types pretty printing

instance Pretty Qual where
  pretty (Qual _ p) = pretty p

prettyPrintAssign :: Assignment -> Doc ann
prettyPrintAssign assign = vsep [ppEntry x p | (x, p) <- Map.toList assign]
  where
    ppEntry x p = hsep [pretty x, "↦", brackets $ fillSep (punctuate "," (ppQual <$> p))]
    ppQual (Qual _ p) = pretty p


instance Pretty LIPred where
  pretty (LIVar i subs) = "κ" <> pretty i <> ppsub
    where
      ppsub = if | Map.null (psubVars subs) && Map.null (psubLocs subs) -> mempty
                 | otherwise -> ppsub0
      mkEntry px e = hsep [px, "↦", pretty e]
      subEntries =
        [hsep [mkEntry (pretty x) e] | (x, e) <- Map.toList (psubVars subs)]
        <> [hsep [mkEntry (pretty l) e] | (l, e) <- Map.toList (psubLocs subs)]
      ppsub0 = brackets (mconcat (punctuate ", " subEntries))
  pretty (LIForm p) = pretty p

instance (Refineable p, Pretty p) => Pretty (LocalEnv p) where
  pretty (LocalEnv vars preds) =
    let pvars = [pretty x <+> "↦" <+> pretty p | (x, p) <- Map.toList vars]
        ppreds = [pretty p | p <- preds]
    in hsep (punctuate "," (pvars ++ ppreds))

instance Pretty PropTag where
  pretty PropNone = "none"
  pretty (PropContractInv _) = "contract invariant"
  pretty PropSafeMath = "safe math"
  pretty PropAssert = "assertion"
  pretty PropFunArg = "function argument"
  pretty PropLoopInv = "loop invariant"

instance (Refineable p, Pretty p) => Pretty (Judgment p) where
  pretty (JTyWellForm env skel) = pretty env <+> "⊨" <+> pretty skel
  pretty (JSubtype env skel1 skel2 (_, propTag)) =
    pretty env <+> "⊨" <+> pretty skel1 <+> "<:" <+> pretty skel2 <> pptag propTag
    where
      pptag = \case
        PropNone -> emptyDoc
        tag -> " " <> braces (pretty tag)

prettySexpr :: SMT.SExpr -> Doc ann
prettySexpr = \case
  SMT.Atom x -> pretty x
  SMT.List l -> parens (plist l)
  where
    alignArgs f args = 
        group (pretty (f :: Text) <+> align (vsep (prettySexpr <$> args)))
    plist :: [SMT.SExpr] -> Doc ann
    plist = \case
      [] -> emptyDoc
      SMT.Atom "and" : rest -> alignArgs "and" rest
      [SMT.Atom "=>", p, q]  ->
        pretty ("=>" :: Text) <+> align (vsep [prettySexpr p, prettySexpr q])
      [SMT.Atom "forall", args, body]  ->
        pretty ("forall" :: Text) <+> align (prettySexpr args) <+> nest 2 (prettySexpr body)
      l -> hsep (prettySexpr <$> l)
