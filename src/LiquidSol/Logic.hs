{-|
  Utility functions for liquid types and logic
-}
module LiquidSol.Logic
  ( Sort(..), skelToSort, rtypeToSort, constSort
  , predSubst, predSubstMany
  , exprToPred
  , skelSubst, rtypeSubst ) where

import Data.Text (Text)
import Data.Map (Map)
import qualified Data.Map as Map

import LiquidSol.Syntax

data Sort
  = SortInt (Maybe Int)
  | SortBool | SortMapping Sort Sort | SortArray Sort (Maybe Integer) | SortStruct Text
  | SortByte
  deriving (Show, Eq, Ord)

skelToSort :: Skel a -> Sort
skelToSort = \case
  TyInt m -> SortInt m
  TyAddress -> SortInt (Just 160)
  TyBool -> SortBool
  TyUnit -> undefined
  TyFunc{} -> undefined
  TyStruct n _ -> SortStruct n
  TyMapping t1 t2 -> SortMapping (skelToSort t1) (skelToSort t2)
  TyArray t msz -> SortArray (skelToSort t) msz
  TyByte -> SortByte

rtypeToSort :: RType a -> Sort
rtypeToSort (RType _ s _) = skelToSort s

constSort :: Constant -> Sort
constSort = \case
  CInt _ -> SortInt Nothing
  CAddress _ -> SortInt (Just 160)
  CBool _ -> SortBool
  CMapZero t1 t2 -> SortMapping (skelToSort t1) (skelToSort t2)
  CArrZero t msz -> SortArray (skelToSort t) msz
  CStruct name _ -> SortStruct name
  CByte _ -> SortByte
  CString _ -> SortArray SortByte Nothing

exprToPred :: Expr -> Pred
exprToPred = \case
  EConst c -> PConst c
  EVar x -> PVar x
  EMapInd e1 e2 -> PMapInd (f e1) (f e2)
  EMapPut e1 e2 e3 -> PMapPut (f e1) (f e2) (f e3)
  ERel r e1 e2 -> PRel r (f e1) (f e2)
  EArith2 a e1 e2 -> PArith2 a (f e1) (f e2)
  EBoolOp op -> case op of
    BAnd e1 e2 -> PAnd (f e1) (f e2)
    BOr e1 e2 -> POr (f e1) (f e2)
    BNot e -> PNot (f e)
  EField e1 x -> PField (f e1) x
  EFieldUpd e1 x e2 -> PFieldUpd (f e1) x (f e2)
  EUnintFn x es -> PUnintFn x (f <$> es)
  EHavoc t -> PHavoc t
  ECast e t -> PCast (f e) t
  where
    f = exprToPred

-- | Predicate expression substitution
predSubst :: Text -> Pred -> Pred -> Pred
predSubst x p = predSubstMany (Map.fromList [(x, p)])

predSubstMany :: Map Text Pred -> Pred -> Pred
predSubstMany sub = \case
  p@PConst{} -> p
  PVar x -> Map.findWithDefault (PVar x) x sub
  PMapInd e1 e2 -> PMapInd (f e1) (f e2)
  PMapPut e1 e2 e3 -> PMapPut (f e1) (f e2) (f e3)
  PRel r e1 e2 -> PRel r (f e1) (f e2)
  PArith2 a e1 e2 -> PArith2 a (f e1) (f e2)
  PAnd p q -> PAnd (f p) (f q)
  POr p q -> POr (f p) (f q)
  PNot p -> PNot (f p)
  PImplies p q -> PImplies (f p) (f q)
  PIff p q -> PIff (f p) (f q)
  PField e1 x -> PField (f e1) x
  PFieldUpd e1 x e2 -> PFieldUpd (f e1) x (f e2)
  PUnintFn x ps -> PUnintFn x (f <$> ps)
  p@PHavoc{} -> p
  PCast p t -> PCast (f p) t
  where
    f = predSubstMany sub

rtypeSubst :: Map Text Pred -> RType Pred -> RType Pred
rtypeSubst sub (RType v t p) =
  RType v (skelSubst sub t) (predSubstMany (Map.delete v sub) p)

skelSubst :: Map Text Pred -> Skel Pred -> Skel Pred
skelSubst sub = \case
  TyInt i -> TyInt i
  TyAddress -> TyAddress
  TyBool -> TyBool
  TyUnit -> TyUnit
  TyByte -> TyByte
  TyFunc x r1 r2 -> TyFunc x (rtypeSubst sub r1) (rtypeSubst (Map.delete x sub) r2)
  TyStruct n flds -> TyStruct n $ go (\sub' (x, t) ->
                                        ((x, rtypeSubst sub' t), Map.delete x sub')) sub flds

  TyArray t msz -> TyArray (skelSubst sub t) msz
  TyMapping t1 t2 -> TyMapping (skelSubst sub t1) (skelSubst sub t2)
  where
    go :: (c -> a -> (b, c)) -> c -> [a] -> [b]
    go f z (x:xs) = let (x', z') = f z x in x' : go f z' xs
    go _ _ [] = []
