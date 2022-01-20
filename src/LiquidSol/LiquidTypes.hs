{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.LiquidTypes where

import Data.Text (Text)
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

import LiquidSol.Syntax
import LiquidSol.Logic (predSubstMany, exprToPred)
import LiquidSol.Util.Unsafe (unsafeLookup)
import Data.Functor (($>))

-- | A qualifier is a "template" for a predicate
data Qual = Qual Text Pred
  deriving (Show, Eq, Ord)

qualToPred :: Pred -> Qual -> Pred
qualToPred v (Qual x p) = predSubstMany (Map.fromList [(x, v)]) p

type Assignment = Map Int [Qual]

assignRType :: Assignment -> RType LIPred -> RType Pred
assignRType assign (RType v ty li) = RType v (assignSkel assign ty) $ case li of
  LIForm p -> p
  LIVar i subs ->
    let quals = [predSubstMany (psubVars subs) (qualToPred (PVar v) q) | q <- assign `unsafeLookup` i] in
      mkConj quals
  where
    mkConj = foldr PAnd PTrue

assignSkel :: Assignment -> Skel LIPred -> Skel Pred
assignSkel assign = \case
  TyStruct name flds -> TyStruct name [(x, assignRType assign t) | (x, t) <- flds]
  TyFunc x t1 t2 -> TyFunc x (assignRType assign t1) (assignRType assign t2)
  TyMapping t1 t2 -> TyMapping (assignSkel assign t1) (assignSkel assign t2)
  TyArray t msz -> TyArray (assignSkel assign t) msz
  TyInt m -> TyInt m
  TyAddress -> TyAddress
  TyBool -> TyBool
  TyByte -> TyByte
  TyUnit -> TyUnit

assignEnv :: Assignment -> LocalEnv LIPred -> LocalEnv Pred
assignEnv assign (LocalEnv vars preds) =
  LocalEnv (Map.map (assignRType assign) vars) preds

assignJudg :: Assignment -> Judgment LIPred -> Judgment Pred
assignJudg assign = \case
  JTyWellForm env t -> JTyWellForm (assignEnv assign env) (assignRType assign t)
  JSubtype env t1 t2 prop ->
    JSubtype (assignEnv assign env) (assignRType assign t1) (assignRType assign t2) prop

-- | Pending substitutions
data PendingSub = PendingSub { psubVars :: Map Text Pred, psubLocs :: Map Loc Pred }
  deriving (Show, Eq, Ord)

instance Semigroup PendingSub where
  p1 <> p2 = PendingSub
    { psubVars = psubVars p1 <> psubVars p2
    , psubLocs = psubLocs p1 <> psubLocs p2
    }

instance Monoid PendingSub where
  mempty = PendingSub { psubVars = Map.empty, psubLocs = Map.empty  }

-- | Liquid type predicate: variable or formula
data LIPred = LIVar Int PendingSub | LIForm Pred
  deriving (Show, Eq, Ord)

-- | Inferred predicate information: vars in scope, then either phi vars or locations
data InfPredType = InfPredOther | InfPredLoop
  deriving (Show, Eq, Ord)

data InfPred = InfPred [(Text, UType)] (Either [(Text, UType)] [Loc]) InfPredType
  deriving (Show)

-- | Liquid type inference unrefined type skeleton
type LISkel = Skel LIPred

-- | Liquid type inference refined type skeleton
type LIRType = RType LIPred

psubAddVar :: Text -> Pred -> PendingSub -> PendingSub
psubAddVar x e psub = psub{psubVars = Map.insert x e (psubVars psub)}

psubAddLoc :: Loc -> Pred -> PendingSub -> PendingSub
psubAddLoc l e psub = psub{psubLocs = Map.insert l e (psubLocs psub)}

psubEmpty :: PendingSub
psubEmpty = PendingSub{psubVars = Map.empty, psubLocs = Map.empty}

applyPendingSub :: PendingSub -> Pred -> Pred
applyPendingSub = predSubstMany . psubVars

pushPendingSub :: PendingSub -> LIRType -> LIRType
pushPendingSub sub skel = flip fmap skel $ \case
  LIVar i ps -> LIVar i (sub <> ps)
  LIForm p -> LIForm (applyPendingSub sub p)

-- | Liquid local environment, containing variable bindings and path conditions
data LocalEnv p = LocalEnv (Map Text (RType p)) [Pred]
  deriving (Show)

type LiLocalEnv = LocalEnv LIPred

solidityGlobalVars :: Refineable p => [(Text, RType p)]
solidityGlobalVars = [msgSender, msgValue, msgData, blockTimestamp, blockNumber, blockDiff, this, txOrigin]
  where
    -- now = ("now", RType "v" (TyInt (Just 256)) (predicate PTrue))
    msgSender = ("$__msg_sender", RType "v" TyAddress (predicate PTrue))
    msgValue = ("$__msg_value", RType "v" (TyInt (Just 256)) (predicate PTrue))
    msgData = ("$__msg_data", RType "v" (TyArray TyByte Nothing) (predicate PTrue))
    blockTimestamp = ("$__block_timestamp", RType "v" (TyInt (Just 256))
                       (predicate (PRel RelLte (PVar "v") (PConst (CInt (2 ^ (128 :: Integer)))))))
    blockNumber = ("$__block_number", RType "v" (TyInt (Just 256)) (predicate PTrue))
    blockDiff = ("$__block_difficulty", RType "v" (TyInt (Just 256)) (predicate PTrue))
    this = ("this", RType "v" TyAddress (predicate PTrue))
    txOrigin = ("$__tx_origin", RType "v" TyAddress (predicate PTrue))

localEnvEmpty :: Refineable p => LocalEnv p
localEnvEmpty = LocalEnv (Map.fromList solidityGlobalVars) []

localEnvMap :: (a -> b) -> LocalEnv a -> LocalEnv b
localEnvMap f (LocalEnv vars ps) = LocalEnv (Map.map (fmap f) vars) ps

localEnvVars :: LocalEnv p -> Map Text (RType p)
localEnvVars (LocalEnv vars _) = vars

localEnvVarAssoc :: LocalEnv p -> [(Text, UType)]
localEnvVarAssoc = Map.toList . localEnvVars . localEnvMap (const ())

localEnvAddPred :: Pred -> LocalEnv p -> LocalEnv p
localEnvAddPred p (LocalEnv vars ps) = LocalEnv vars (p : ps)

localEnvUpdateVar :: Text -> RType p -> LocalEnv p -> LocalEnv p
localEnvUpdateVar x t (LocalEnv vars ps) = LocalEnv (Map.insert x t vars) ps

localEnvLookup :: Text -> LocalEnv p -> Maybe (RType p)
localEnvLookup x (LocalEnv vars _) = Map.lookup x vars

-- | Liquid global environment, containing storage locations and checked out
-- storage variables.
data GlobalEnv p = GlobalEnv (Map Loc (Text, RType p)) (Map Loc Text)
  deriving (Show)

globalEnvEmpty :: GlobalEnv p
globalEnvEmpty = GlobalEnv Map.empty Map.empty

globalEnvUpdateLoc :: Loc -> Text -> RType p -> GlobalEnv p -> GlobalEnv p
globalEnvUpdateLoc l x s (GlobalEnv locs vars) = GlobalEnv (Map.insert l (x, s) locs) vars

globalEnvLookupLoc :: Loc -> GlobalEnv p -> Maybe (RType p)
globalEnvLookupLoc l (GlobalEnv locs _) = snd <$> Map.lookup l locs

globalEnvLookupLocVar :: Loc -> GlobalEnv p -> Maybe Text
globalEnvLookupLocVar l (GlobalEnv locs _) = fst <$> Map.lookup l locs

globalEnvLocSet :: GlobalEnv p -> Set Loc
globalEnvLocSet (GlobalEnv locs _) = Map.keysSet locs

globalEnvClearCheckout :: GlobalEnv p -> GlobalEnv p
globalEnvClearCheckout (GlobalEnv locs _) = GlobalEnv locs mempty

globalEnvSetCheckout :: Loc -> Text -> GlobalEnv p -> GlobalEnv p
globalEnvSetCheckout l x (GlobalEnv locs vars) = GlobalEnv locs (Map.insert l x vars)

globalEnvStoVarMap :: GlobalEnv p -> Map Text (RType p)
globalEnvStoVarMap (GlobalEnv locs _) =
  Map.fromList [(x, t) | (x, t) <- Map.elems locs]

type LiGlobalEnv = GlobalEnv LIPred

-- | ACTUAL global environment containing function signatures and struct definitions
--
-- TODO: refactor this and global env
data Delta p = Delta
  { delta_structs :: Map Text [(Text, RType p)]
  , delta_funs :: Map Text ([(Text, RType p)], [(Text, RType p)], Mutability) }
  deriving (Show, Eq, Ord)

deltaEmpty :: Delta p
deltaEmpty = Delta { delta_structs = Map.empty, delta_funs = Map.empty }

deltaResolveSkel :: Skel p -> Delta p -> Maybe (Skel p)
deltaResolveSkel t delta = case t of
  TyFunc{} -> pure t -- TODO: resolve properly
  TyStruct name _ -> fmap (TyStruct name) (Map.lookup name (delta_structs delta))
  TyMapping t1 t2 -> TyMapping <$> deltaResolveSkel t1 delta <*> deltaResolveSkel t2 delta
  TyArray t1 msz -> TyArray <$> deltaResolveSkel t1 delta <*> pure msz
  _ -> Just t

type LiDelta = Delta LIPred

data PropTag
  = PropNone -- ^ Nothing special about this.
  | PropSafeMath -- ^ This is a safe math property.
  | PropAssert -- ^ This is an assertion.
  | PropContractInv Bool -- ^ This is a contract invariant. True if in constructor, false otherwise.
  | PropLoopInv -- ^ This is a loop invariant.
  | PropFunArg -- ^ This is a function precondition.
  deriving (Show, Eq)

-- | Location of generated constraint
type SrcTag = Maybe (Text, Maybe SrcLoc)

-- | Liquid type judgments
data Judgment p
  = -- | Type well-formedness judgment
    JTyWellForm (LocalEnv p) (RType p)
  | -- | Subtyping judgment
    JSubtype (LocalEnv p) (RType p) (RType p) (SrcTag, PropTag)
  deriving (Show)

type LiJudgment = Judgment LIPred

liRTypeFreeVars :: LIRType -> Set Int
liRTypeFreeVars (RType _ t p) = liSkelFreeVars t <> case p of
  LIVar i _ -> Set.singleton i
  _ -> Set.empty

-- | Free liquid type variables
liSkelFreeVars :: LISkel -> Set Int
liSkelFreeVars = \case
  TyFunc _ r1 r2 -> liRTypeFreeVars r1 `Set.union` liRTypeFreeVars r2
  TyStruct _ flds -> mconcat [liRTypeFreeVars t | (_, t) <- flds]
  TyMapping t1 t2 -> liSkelFreeVars t1 <> liSkelFreeVars t2
  TyArray t _ -> liSkelFreeVars t
  _ -> Set.empty

-- | Free liquid type variables
liJudgmentFreeVars :: LiJudgment -> Set Int
liJudgmentFreeVars = \case
  JTyWellForm (LocalEnv vars _) skel ->
    let envFv = mconcat [liRTypeFreeVars s | s <- Map.elems vars] in
      envFv `Set.union` liRTypeFreeVars skel
  JSubtype (LocalEnv vars _) skel1 skel2 _ ->
    let envFv = mconcat [liRTypeFreeVars s | s <- Map.elems vars] in
      envFv `Set.union` liRTypeFreeVars skel1 `Set.union` liRTypeFreeVars skel2

-- | Type class for refinable types
class Refineable p where
  predicate :: Pred -> p
  predicateIsTrue :: p -> Bool

instance Refineable () where
  predicate = const ()
  predicateIsTrue = const True

instance Refineable Pred where
  predicate = id
  predicateIsTrue = const True

instance Refineable LIPred where
  predicate = LIForm
  predicateIsTrue = \case
    LIForm PTrue -> True
    _ -> False

-- | Generate a skeleton with predicate true.
shapeSkel :: Refineable p => Skel a -> Skel p
shapeSkel = fmap (const (predicate PTrue))

-- | Convert a skeleton back into one with no refinement.
skelToUskel :: Skel a -> USkel
skelToUskel s = s $> ()

-- | Refinement type equal to expression
exprSkel :: Refineable p => Skel p -> Expr -> RType p
exprSkel t e = RType "v" t (predicate (PRel RelEq (PVar "v") (exprToPred e)))

constType :: Refineable p => Constant -> RType p
constType c = mkConst $ case c of
  CInt _ -> TyInt Nothing
  CAddress _ -> TyAddress
  CBool _ -> TyBool
  CMapZero t1 t2 -> TyMapping (shapeSkel t1) (shapeSkel t2)
  CArrZero t msz -> TyArray (shapeSkel t) msz
  CStruct name flds -> TyStruct name [(x, constType cx) | (x, cx) <- flds]
  CString _ -> TyArray TyByte Nothing
  CByte _ -> TyByte
  where
    mkConst ty = exprSkel ty (EConst c)
