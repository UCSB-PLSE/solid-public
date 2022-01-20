{-# LANGUAGE OverloadedStrings, DerivingStrategies, DeriveAnyClass #-}
module LiquidSol.Syntax
    ( Rel(..), Arith2(..), Constant(..), BoolOp(..)
    , Expr(..), isValue, exprSubst, exprSubstMany, exprReplace
    , Pred(..), pattern PTrue, pattern PFalse, predReplace
    , Annot(..)
    , LValue(..), lvalueToExpr, lvalueFirst, lvalueReplaceFirst
    , PhiNode, Stmt(..)
    , Block, blockStmts, mapBlockStmts, traverseBlock, takeUntilReturn
    , Skel(..), RType(..), USkel, UType, rtypeSkel
    , skelIntMerge, shape, skelEq, zeroValue
    , Loc(..), Visibility(..), Mutability(..), Decl(..), Contract(..)
    , SrcLoc(..), noSrcLoc, predAndMany) where

import Control.Monad (forM, join)
import Data.Text (Text)
import Data.Maybe (fromMaybe)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import GHC.Generics (Generic, Generic1)
import Control.DeepSeq (NFData, NFData1)
import LiquidSol.SrcLoc (SrcLoc(..), noSrcLoc)
import Data.Bifunctor (second)

-- | Relations
data Rel = RelGt | RelGte | RelEq | RelLt | RelLte | RelNeq
  deriving (Show, Eq, Ord, Generic, NFData)

-- | Binary arithmetic operators
data Arith2
  = AAdd
  | ASub
  | AMul
  | ADiv
  | AMod
  | AAddMod
  deriving (Show, Eq, Ord, Generic, NFData)

data Constant
  = CInt Integer
  | CAddress Integer
  | CBool Bool
  | CMapZero USkel USkel
  | CArrZero USkel (Maybe Integer)
  | CStruct Text [(Text, Constant)]
  | CString Text
  | CByte Int
  deriving (Show, Eq, Ord, Generic, NFData)

data BoolOp
  = BAnd Expr Expr
  | BOr Expr Expr
  | BNot Expr
  deriving (Show, Eq, Ord, Generic, NFData)

data Expr
  = EConst Constant
  | EVar Text
  | EMapInd Expr Expr
  | EMapPut Expr Expr Expr
  | ERel Rel Expr Expr
  | EArith2 Arith2 Expr Expr
  | EBoolOp BoolOp
  | EField Expr Text
  | EFieldUpd Expr Text Expr
  | EUnintFn Text [Expr]
  | EHavoc USkel
  | ECast Expr USkel
  deriving (Show, Eq, Ord, Generic, NFData)

-- | Symbolic predicate
data Pred
  = PConst Constant
  | PVar Text
  | PMapInd Pred Pred
  | PMapPut Pred Pred Pred
  | PRel Rel Pred Pred
  | PArith2 Arith2 Pred Pred
  | PAnd Pred Pred
  | POr Pred Pred
  | PNot Pred
  | PImplies Pred Pred
  | PIff Pred Pred
  {-  | PForAll Text USkel Pred -}
  | PField Pred Text
  | PFieldUpd Pred Text Pred
  | PUnintFn Text [Pred]
  | PHavoc USkel
  | PCast Pred USkel
  deriving (Show, Eq, Ord, Generic, NFData)

pattern PTrue :: Pred
pattern PTrue = PConst (CBool True)

pattern PFalse :: Pred
pattern PFalse = PConst (CBool False)

predAndMany :: [Pred] -> Pred
predAndMany [] = PTrue
predAndMany (x:xs) = case x of
  PTrue -> predAndMany xs
  _ -> PAnd x (predAndMany xs)

isValue :: Expr -> Bool
isValue = \case
  EConst _ -> True
  EVar _ -> True
  _ -> False

-- | Replace every expression node
exprReplace :: (Expr -> Expr) -> Expr -> Expr
exprReplace f = f . \case
  e@EConst{} -> e
  e@EVar{} -> e
  EMapInd e1 e2 -> EMapInd (recur e1) (recur e2)
  EMapPut e1 ei ev -> EMapPut (recur e1) (recur ei) (recur ev)
  ERel r e1 e2 -> ERel r (recur e1) (recur e2)
  EArith2 a e1 e2 -> EArith2 a (recur e1) (recur e2)
  EField e fld -> EField (recur e) fld
  EFieldUpd e fld ef -> EFieldUpd (recur e) fld (recur ef)
  EUnintFn fn args -> EUnintFn fn (recur <$> args)
  EBoolOp bop -> EBoolOp $ case bop of
    BAnd e1 e2 -> BAnd (recur e1) (recur e2)
    BOr e1 e2 -> BOr (recur e1) (recur e2)
    BNot e1-> BNot (recur e1)
  e@EHavoc{} -> e
  ECast e ty -> ECast (recur e) ty
  where
    recur = exprReplace f

predReplace :: (Pred -> Pred) -> Pred -> Pred
predReplace f = f . \case
  e@PConst{} -> e
  e@PVar{} -> e
  PMapInd e1 e2 -> PMapInd (recur e1) (recur e2)
  PMapPut e1 ei ev -> PMapPut (recur e1) (recur ei) (recur ev)
  PRel r e1 e2 -> PRel r (recur e1) (recur e2)
  PArith2 a e1 e2 -> PArith2 a (recur e1) (recur e2)
  PField e fld -> PField (recur e) fld
  PFieldUpd e fld ef -> PFieldUpd (recur e) fld (recur ef)
  PUnintFn fn args -> PUnintFn fn (recur <$> args)
  PAnd e1 e2 -> PAnd (recur e1) (recur e2)
  POr e1 e2 -> POr (recur e1) (recur e2)
  PNot e1-> PNot (recur e1)
  PIff e1 e2 -> PIff (recur e1) (recur e2)
  PImplies e1 e2 -> PImplies (recur e1) (recur e2)
  e@PHavoc{} -> e
  PCast e ty -> PCast (recur e) ty
  where
    recur = predReplace f

-- | Expression substitution
exprSubst :: Text -> Expr -> Expr -> Expr
exprSubst x e = exprSubstMany (Map.fromList [(x, e)])

exprSubstMany :: Map Text Expr -> Expr -> Expr
exprSubstMany sub = exprReplace f
  where
    f = \case
      EVar y -> case Map.lookup y sub of
        Just e -> e
        Nothing -> EVar y
      e -> e

-- | Type skeleton
data Skel a
  = TyInt (Maybe Int)
  | TyBool
  | TyUnit
  | TyByte
  | TyFunc !Text !(RType a) !(RType a)
  | TyStruct !Text [(Text, RType a)]
  | TyMapping (Skel a) (Skel a)
  | TyArray (Skel a) (Maybe Integer)
  | TyAddress
  deriving (Show, Eq, Ord, Functor, Generic, Generic1, NFData, NFData1)

skelIntMerge :: Maybe Int -> Maybe Int -> Maybe Int
skelIntMerge Nothing m = m
skelIntMerge m Nothing = m
skelIntMerge (Just n1) (Just n2) = Just (max n1 n2)

-- | Refined type skeleton
data RType a = RType !Text (Skel a) a
  deriving (Show, Eq, Ord, Functor, Generic, Generic1, NFData, NFData1)

rtypeSkel :: RType a -> Skel a
rtypeSkel (RType _ a _) = a

-- | Unrefined type skeleton
type USkel = Skel ()
-- | Unrefined refined type skeleton (no predicates)
type UType = RType ()

shape :: Functor f => f a -> f ()
shape = fmap (const ())

-- | Skeleton equality only, ignoring predicates
skelEq :: Skel a -> Skel a -> Bool
skelEq t1 t2
  | TyInt m1 <- t1, TyInt m2 <- t2 =
      if | Nothing <- m1 -> True
         | Nothing <- m2 -> True
         | otherwise -> m1 == m2
  | TyBool <- t1, TyBool <- t2 = True
  | TyByte <- t1, TyByte <- t2 = True
  | TyAddress <- t1, TyAddress <- t2 = True
  | TyStruct n1 _ <- t1, TyStruct n2 _ <- t2, n1 == n2 = True
  | TyArray t1' sz1 <- t1, TyArray t2' sz2 <- t2, sz1 == sz2 = skelEq t1' t2'
  | TyMapping ta tb <- t1, TyMapping ta' tb' <- t2 = skelEq ta ta' && skelEq tb tb'
  | otherwise = False

zeroValue :: Skel a -> Constant
zeroValue = \case
  TyAddress -> CAddress 0
  TyInt _ -> CInt 0
  TyBool -> CBool False
  TyUnit -> error "zeroValue: unit has no zero value"
  TyFunc{} -> error "zeroValue: function has no zero value"
  TyStruct name fields -> CStruct name [(n, zeroValue t) | (n, RType _ t _) <- fields]
  TyMapping t1 t2 -> CMapZero (shape t1) (shape t2)
  TyArray t msz -> CArrZero (shape t) (Just (fromMaybe 0 msz))
  TyByte -> CByte 0

-- | Liquid type solver annotation
data Annot
  = -- | Liquid type implication assertion
    ASubtype Text (RType Pred)
  | -- | Liquid type ascription (use instead of inference)
    AAscribe Text (RType Pred)
  | -- | Liquid type path condition assumption
    AAssume Pred
  | -- | Reachability check (TODO)
    AReachable
  | -- | Add qualifier (with other vars instantiated)
    ADefQual Text [Text] Pred
  | -- | Reorder phi nodes
    APhiReorder [Text]
  deriving (Show, Eq, Ord, Generic, NFData)

-- | l-value (assignable expression)
data LValue
  = LvVar Text
  | LvInd LValue Expr
  | LvFld LValue Text
  deriving (Show, Eq, Ord, Generic, NFData)

lvalueToExpr :: LValue -> Expr
lvalueToExpr = \case
  LvVar x -> EVar x
  LvInd lv e -> EMapInd (lvalueToExpr lv) e
  LvFld lv f -> EField (lvalueToExpr lv) f

lvalueFirst :: LValue -> Text
lvalueFirst = \case
  LvVar x -> x
  LvInd lv _ -> lvalueFirst lv
  LvFld lv _ -> lvalueFirst lv

lvalueReplaceFirst :: Text -> LValue -> LValue
lvalueReplaceFirst x = \case
  LvVar _ -> LvVar x
  LvInd lv e -> LvInd (lvalueReplaceFirst x lv) e
  LvFld lv f -> LvFld (lvalueReplaceFirst x lv) f

type PhiNode p = [(Text, RType p, [Text])]

-- | Statements
data Stmt p
  = -- | Variable declaration and assignment
    SDecl Text (RType p) (Maybe Expr)
  | -- | Variable assignment (with optional index)
    SAsn LValue Expr
  | -- | Function call (with optional assignment)
    SCall [(Text, RType p)] Text [Expr]
  | -- | "Let" if-else statement (with optional else)
    SIf (PhiNode p) Expr (Block p) (Block p)
  | -- | While loop
    SWhile (PhiNode p) Expr (Block p)
  | -- | Fetch from storage (not user-visible). Bool is true if declare, false if assign (purely cosmetic).
    SFetch [(Text, RType p, Loc)] Bool
  | -- | Commit to storage (not user-visible)
    SCommit [(Loc, Expr)]
  | -- | Solver annotation
    SAnnot Annot
  | -- | Return
    SReturn [Expr]
  | -- | Havoc (to model unsupported features)
    SHavoc
  | -- | Abort
    SAbort
  deriving (Show, Eq, Ord, Functor, Generic, NFData)

type Block p = [(SrcLoc, Stmt p)]
-- type Block p = [Stmt p]

blockStmts :: Block p -> [Stmt p]
blockStmts b = snd <$> b

mapBlockStmts :: (Stmt p -> Stmt p) -> Block p -> Block p
mapBlockStmts f b = second f <$> b

traverseBlock :: (Monad m) => (Stmt p -> m [a]) -> Block p -> m [(SrcLoc, a)]
traverseBlock f b =
  fmap join . forM b $ \(srcloc, s) -> do
    stmts <- f s
    pure ((srcloc,) <$> stmts)

-- | Take statements until a return or abort is reached. Indicates True if so.
takeUntilReturn :: Block p -> (Block p, Bool)
takeUntilReturn = \case
  [] -> ([], False)
  (x:xs) -> case x of
    (_, SReturn _) -> ([x], True)
    (_, SAbort) -> ([x], True)
    _ -> let (xs', es) = takeUntilReturn xs in (x : xs', es)

newtype Loc = Loc Int
  deriving (Show, Eq, Ord, Generic)
  deriving newtype NFData

data Visibility = VisInt | VisExt
  deriving (Show, Eq, Ord, Generic, NFData)

data Mutability = MutStateless | MutReadonly | MutStateful
  deriving (Show, Eq, Ord, Generic, NFData)

-- | Smart contract declarations
data Decl p
  = DVar Text (RType p) (Maybe Expr) Loc
  | DFun { dfun_name :: Text
         , dfun_args :: [(Text, RType p)]
         , dfun_res :: [(Text, RType p)]
         , dfun_body :: Block p
         , dfun_vis :: Visibility
         , dfun_loc :: SrcLoc
         , dfun_mut :: Mutability }
  | DCtor { dctor_args :: [(Text, RType p)]
          , dctor_body :: Block p
          , dctor_loc :: SrcLoc }
  | DStruct { dsct_name :: Text
            , dsct_fields :: [(Text, RType p)] }
  | DAnnot Annot
  deriving (Show, Eq, Ord, Functor, Generic, Generic1, NFData)

data Contract p
  = Contract Text [Decl p]
  deriving (Show, Eq, Ord, Functor, Generic, Generic1, NFData)
