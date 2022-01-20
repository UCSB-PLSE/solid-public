module LiquidSol.SmtProcs where

import qualified SimpleSMT as S
import Data.Text.Prettyprint.Doc (pretty)
import qualified Data.Text.Prettyprint.Doc as PP

-- | Compute the maximum universal subset of a formula using cardinality as a
-- cost function
--
-- TODO: speed this up with dynamic programming
findMUS :: S.Solver -> S.SExpr -> [String] -> IO [String]
findMUS solver phi vars_ = go vars_ []
  where
    go [] _ = pure []
    go (x:xs) uvars = do
      let p = sForall [(y, S.tInt) | y <- (x:uvars)] phi
      S.push solver
      S.assert solver p
      result <- S.check solver
      S.pop solver
      best <- case result of
        S.Sat -> (x:) <$> go xs (x:uvars)
        _ -> pure []
      best' <- go xs uvars
      pure $ if length best > length best' then best else best'

sForall :: [(String, S.SExpr)] -> S.SExpr -> S.SExpr
sForall xs p = S.fun "forall" [S.List [S.List [S.Atom x, s]  | (x, s) <- xs], p]

declareSort :: S.Solver -> String -> Int -> IO S.SExpr
declareSort solver name arity =
  S.ackCommand solver (S.fun "declare-sort" [S.Atom name, S.Atom (show arity)]) *> pure (S.const name)

defineSort :: S.Solver -> String -> S.SExpr -> IO S.SExpr
defineSort solver name sort =
  S.ackCommand solver (S.fun "define-sort" [S.Atom name, S.List [], sort]) *> pure (S.const name)

arrayConst :: S.SExpr -> S.SExpr -> S.SExpr
arrayConst sort value = S.List [S.fun "as" [S.const "const", sort], value]

nat2bv :: Integer -> S.SExpr -> S.SExpr
nat2bv b e = S.List [S.fun "_" [S.const "int2bv", S.int b], e]

bv2nat :: S.SExpr -> S.SExpr
bv2nat e = S.fun "bv2int" [e]

ppSExpr :: S.SExpr -> PP.Doc ann
ppSExpr = \case
  S.Atom x -> pretty x
  S.List ls -> PP.parens $ case ls of
    [S.Atom "forall", params, body] ->
      pretty "forall" PP.<+> PP.align (PP.group (ppSExpr params)) <> PP.hardline <> ppSExpr body
    S.Atom k:_ | k `elem` ["and", "or"] -> sepAlignFirst (ppSExpr <$> ls)
    [S.Atom "=>", p, q] -> pretty "=>" PP.<+> PP.align (mconcat [ppSExpr p, PP.hardline, ppSExpr q])
    _ -> PP.group (PP.fillSep (ppSExpr <$> ls))
  where
    sepAlignFirst = \case
      (d:ds) -> d PP.<+> PP.align (PP.fillSep ds)
      ds -> PP.fillSep ds
