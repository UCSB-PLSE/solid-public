{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-deferred-type-errors #-}
module LiquidSol.InvGen where

import LiquidSol.LiquidTypes
import LiquidSol.Syntax
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Map as Map

import LiquidSol.SortCheck
import LiquidSol.Logic (skelToSort, Sort(..))
import qualified Data.Set as Set
import Data.Maybe (isJust)
import qualified LiquidSol.AggProps as Agg
import LiquidSol.PrettyPrint ()
import qualified Data.DList as DList

-- * Invariant candidate generation

-- | Generate well-typed invariant candidates from storage variable information
genInv
  :: Map Text USkel -- ^ storage variables and their types
  -> Delta () -- ^ global definitions
  -> Int -- ^ predicate depth
  -> [Pred]
genInv stoVars delta depth =
  go depth (Set.fromList (PVar <$> Map.keys stoVars))
  where
    sortEnv = SortEnv (Map.map skelToSort stoVars) delta
    isWellSorted e = isJust $ getPredSort e sortEnv
    go 0 exprs = filter (\p -> getPredSort p sortEnv == Just SortBool) $
      genPred stoVars (Set.toList exprs)
    go k exprs =
      -- Generate additional well-sorted expressions & recurse
      let exprs' = Set.fromList . filter isWellSorted $ genExpr Map.empty (Set.toList exprs) in
      go (k - 1) (Set.union exprs exprs')

-- | Generate predicates (i.e. expressions of type bool) given a set of seed
-- expressions
genPred :: Map Text USkel -> [Pred] -> [Pred]
genPred _env terms = DList.toList $
  DList.fromList [PRel r e1 e2 | r <- rels, e1 <- terms, e2 <- terms, e1 /= e2]
  <>
  DList.fromList [PRel RelGt e1 (PConst (CInt 0)) | e1 <- terms]
  where
    rels = [RelLt, RelLte]

-- | Generate more complex expressions from the given set of expressions
genExpr :: Map Text USkel -> [Pred] -> [Pred]
genExpr _env terms =
  [PArith2 op e1 e2 | op <- binops, e1 <- terms, e2 <- terms, e1 /= e2]
  <>
  [PUnintFn "sum" [e] | e <- terms]
  where
    binops = [AAdd]

-- | Generate well-typed sum invariant candidates from storage variable information
genSumInvs
  :: Delta d
  -> Map Text USkel -- ^ storage variables and their types
  -> [Pred]
genSumInvs delta stoVars = cands
  where
    stoVarSorts = Map.map skelToSort stoVars
    mappingTerms = flip Map.mapMaybeWithKey stoVarSorts $ \xm -> \case
      SortMapping _ valSort ->
        let paths = Set.toList $ Set.map Agg.M $ Agg.splitSortPath delta valSort
            sumTerms = Agg.pathToPred <$> paths
            nnzTerms = concatMap Agg.pathToNnz paths
            allTerms = sumTerms <> nnzTerms in
          if null allTerms
            then Nothing
            else Just (($ PVar xm) <$> allTerms)
      _ -> Nothing
    intVars = Map.keys $ flip Map.filter stoVarSorts $ \case
      SortInt{} -> True
      _ -> False
    cands =
      [ PRel RelLte t1 t2
      | t1 <- mconcat (Map.elems mappingTerms)
      , t2 <- mconcat (Map.elems mappingTerms) -- <> (PVar <$> intVars)
      , t1 /= t2 ]
