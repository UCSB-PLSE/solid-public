{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.AggProps where

import LiquidSol.Syntax
import Data.Set (Set)
import qualified Data.Set as Set
import LiquidSol.LiquidTypes
import qualified Data.Map as Map
import Data.Text (Text)
import LiquidSol.Logic (Sort(..), skelToSort)
import qualified Data.Text as Text

-- | Path to nested data types
data PathOp = M PathOp | S Text Text PathOp | I
  deriving (Show, Eq, Ord)

-- | Convert a type into a set of paths to its constituent elements
splitPath :: Delta a -> Skel b -> Set PathOp
splitPath delta = splitSortPath delta . skelToSort

-- | Convert a sort into a set of paths to its constituent elements
splitSortPath :: Delta a -> Sort -> Set PathOp
splitSortPath delta = \case
  SortMapping _ t -> Set.map M (splitSortPath delta t)
  SortStruct n
    | Just flds <- Map.lookup n (delta_structs delta) ->
      let fldPaths t = splitPath delta (rtypeSkel t)
       in mconcat ((\(f, t) -> Set.map (S n f) (fldPaths t)) <$> flds)
  SortInt _ -> Set.singleton I
  _ -> Set.empty

-- | Convert paths to uninterpreted functions over predicates
pathToPred :: PathOp -> (Pred -> Pred)
pathToPred = \case
  M (M p) -> pathToPred (M p) . mkFun "flatten"
  M I -> mkFun "sum"
  M (S n f p) -> pathToPred (M p) . mkFldFun n f
  S _ f p -> \e -> pathToPred p (PField e f)
  I -> id
  where
    mkFun name arg = PUnintFn name [arg]
    mkFldFun n f arg = PUnintFn "fld" [PVar n, PVar f, arg]

-- | Extract path from the argument to a sum
sumPredToPath :: Pred -> (Pred, PathOp)
sumPredToPath = go id
  where
    go k =
     \case
       PUnintFn "flatten" [p] ->
         let (p', path) = go (M . k) p in
           (p', path)
       PUnintFn "fld" [PVar n, PVar f, p] ->
         let (p', path) = go (S n f . k) p in
           (p', path)
       p -> (p, k I)

-- | Convert path of mapping value to ghost variable
pathToGhostVar :: String -> PathOp -> String
pathToGhostVar prefix = (prefix <>) . Text.unpack . go
  where
    go = \case
      M p -> go p <> "_flatten"
      S n f p -> go p <> "_fld:" <> n <> ":" <> f
      I -> ""

pathToNnz :: PathOp -> [Pred -> Pred]
pathToNnz = \case
  M I -> [\e -> PUnintFn "nnz" [e]]
  _ -> []
