module LiquidSol.AstAnalysis
  ( allVarsVarDecl, allVarsExpr, allVarsStmt, allVarsDecl
  , scanAssigns, scanAscriptions, hasGlobl ) where

import Data.Set (Set)
import qualified Data.Set as Set
-- import Data.Map (Map)
-- import qualified Data.Map as Map
import Data.Text (Text)
import Data.Maybe (catMaybes)

import LiquidSol.Syntax

-- | Get all variables defined and used in a variable declaration
allVarsVarDecl :: Text -> Maybe Expr -> Set Text
allVarsVarDecl x exprM =
  let exprFv = maybe Set.empty allVarsExpr exprM in
    Set.singleton x `Set.union` exprFv

-- | Get all variables and used in an expression
allVarsExpr :: Expr -> Set Text
allVarsExpr = \case
  EVar x -> Set.singleton x
  ERel _ e1 e2 -> allVarsExpr e1 <> allVarsExpr e2
  EArith2 _ e1 e2 -> allVarsExpr e1 <> allVarsExpr e2
  EBoolOp bop -> case bop of
    BAnd e1 e2 -> allVarsExpr e1 <> allVarsExpr e2
    BOr e1 e2 -> allVarsExpr e1 <> allVarsExpr e2
    BNot e1 -> allVarsExpr e1
  EConst _ -> Set.empty
  EMapInd e1 e2 -> allVarsExpr e1 <> allVarsExpr e2
  EMapPut e1 e2 e3 -> allVarsExpr e1 <> allVarsExpr e2 <> allVarsExpr e3
  EField e _ -> allVarsExpr e
  EFieldUpd e _ ef -> allVarsExpr e <> allVarsExpr ef
  EUnintFn _ es -> mconcat (allVarsExpr <$> es)
  EHavoc _ -> mempty
  ECast e _ -> allVarsExpr e

allVarsLvalue :: LValue -> Set Text
allVarsLvalue = \case
  LvVar x -> Set.singleton x
  LvInd l e -> allVarsLvalue l <> allVarsExpr e
  LvFld l _ -> allVarsLvalue l

allVarsPhi :: PhiNode p -> Set Text
allVarsPhi phi = Set.fromList [x | (x, _, _) <- phi]

-- | Get all variables defined and used in a statement
allVarsStmt :: Stmt p -> Set Text
allVarsStmt = \case
  SDecl x _ exprM -> allVarsVarDecl x exprM
  SAsn lv e -> allVarsLvalue lv <> allVarsExpr e
  SCall decls _ args ->
    Set.fromList (fst <$> decls) <> mconcat (allVarsExpr <$> args)
  SIf phi e b1 b2 ->
    let vb1 = mconcat (allVarsStmt <$> blockStmts b1)
        vb2 = mconcat (allVarsStmt <$> blockStmts b2) in
      allVarsPhi phi <> allVarsExpr e <> vb1 <> vb2
  SWhile phi e body ->
    let vb = mconcat (allVarsStmt <$> blockStmts body) in
      allVarsPhi phi <> allVarsExpr e <> vb
  SFetch fs _ -> Set.fromList [x | (x, _, _) <- fs]
  SCommit es -> mconcat [allVarsExpr e | (_, e) <- es]
  SAnnot{} -> Set.empty
  SReturn es -> mconcat (allVarsExpr <$> es)
  SHavoc -> Set.empty
  SAbort -> Set.empty

-- | Get all variables defined and used in a declaration
allVarsDecl :: Decl p -> Set Text
allVarsDecl = \case
  DVar x _ exprM _ -> allVarsVarDecl x exprM
  DFun { dfun_args = args, dfun_body = body } ->
    Set.fromList [x | (x, _) <- args] `Set.union` mconcat (allVarsStmt <$> blockStmts body)
  DCtor { dctor_args = args, dctor_body = body } ->
    Set.fromList [x | (x, _) <- args] `Set.union` mconcat (allVarsStmt <$> blockStmts body)
  DStruct{} -> Set.empty
  DAnnot{} -> Set.empty

-- | Whether a statement invalidating the storage variable properties is here
-- (e.g. function call, havoc, etc.)
hasGlobl :: Stmt p -> Bool
hasGlobl = \case
  SIf _ _ b1 b2 -> any hasGlobl (blockStmts b1) || any hasGlobl (blockStmts b2)
  SWhile _ _ b -> any hasGlobl (blockStmts b)
  SCall{} -> True
  SHavoc{} -> True
  _ -> False

-- | Scan statement for variable assignments
scanAssigns :: Stmt p -> Set Text
scanAssigns = \case
  SAsn lv _ -> Set.singleton (lvalueFirst lv)
  SIf _ _ b1 b2 ->
    let a1 = scanAssigns <$> blockStmts b1
        a2 = scanAssigns <$> blockStmts b2 in
      mconcat (a1 ++ a2)
  SWhile _ _ b -> mconcat (scanAssigns <$> blockStmts b)
  SFetch fs _ -> Set.fromList [x | (x, _, _) <- fs]
  _ -> Set.empty

-- | Scan a block for type ascription annotations (non-recursive)
scanAscriptions :: Block p -> [(Text, RType Pred)]
scanAscriptions = catMaybes . fmap f . blockStmts
  where
    f = \case
      SAnnot (AAscribe x t) -> Just (x, t)
      _ -> Nothing
