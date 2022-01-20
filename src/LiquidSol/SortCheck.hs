{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
module LiquidSol.SortCheck
  ( getExprSort
  , getPredSort
  , SortEnv(..),tcEnvToSortEnv) where

import Control.Applicative (Alternative, empty)
import Data.Functor.Identity
import Data.Text (Text)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Control.Monad.Reader
import Control.Monad.Trans.Maybe

import LiquidSol.Logic
import LiquidSol.LiquidTypes (Delta(..), LocalEnv, localEnvVars)
import LiquidSol.Syntax (skelIntMerge, Expr(..), Pred(..), Rel(..), RType(RType))
import Control.Monad.Extra (unlessM)

data SortEnv = SortEnv { sortEnv_vars :: Map Text Sort, sortEnv_delta :: Delta () }
  deriving (Show, Ord, Eq)

newtype SortCheckT m a = SortCheckT { runSortCheckT :: ReaderT SortEnv (MaybeT m) a }
  deriving (Functor, Applicative, Alternative, Monad, MonadReader SortEnv)

type SortCheck a = SortCheckT Identity a

instance MonadTrans SortCheckT where
  lift = lift
  {-# INLINE lift #-}

instance Monad m => MonadPlus (SortCheckT m) where
  mzero = SortCheckT (lift mzero)
  mplus (SortCheckT ma) (SortCheckT mb) = SortCheckT (mplus ma mb)
  {-# INLINE mplus #-}

liftAsks :: Monad m => (SortEnv -> Maybe a) -> SortCheckT m a
liftAsks f = SortCheckT (ReaderT (MaybeT . pure . f))

assertEq :: Monad m => Bool -> Sort -> SortCheckT m Sort
assertEq cond result = if cond then pure result else empty

predSort :: Monad m => Pred -> SortCheckT m Sort
predSort = \case
  PConst c -> pure (constSort c)
  PVar x -> liftAsks (Map.lookup x . sortEnv_vars)
  PMapInd em ei -> do
    sm <- predSort em
    si <- predSort ei
    case sm of
      SortMapping (SortInt _) s2 | SortInt _ <- si -> pure s2
      SortMapping s1 s2 | s1 == si -> pure s2
      SortArray sv _ | SortInt _ <- si -> pure sv
      _ -> empty
  PMapPut em ei ev -> do
    sm <- predSort em
    si <- predSort ei
    sv <- predSort ev
    let isArr = case sm of
          SortArray _ _ | SortInt _ <- si -> True
          _ -> False
    assertEq (sm == SortMapping si sv || isArr) sm
  PArith2 _ e1 e2 -> do
    s1 <- predSort e1
    s2 <- predSort e2
    if | SortInt m1 <- s1, SortInt m2 <- s2 -> pure (SortInt (skelIntMerge m1 m2))
       | otherwise -> empty
  PAnd p q -> twoBoolSort p q
  POr p q -> twoBoolSort p q
  PNot p -> predSort p
  PImplies p q -> twoBoolSort p q
  PIff p q -> twoBoolSort p q
  PRel op e1 e2 -> do
    s1 <- predSort e1
    s2 <- predSort e2
    let cond = if | SortInt _ <- s1, SortInt _ <- s2 -> True
                  | op == RelEq -> s1 == s2
                  | otherwise -> False
    assertEq cond SortBool
  PField e f -> predSort e >>= \case
    SortStruct name ->
      let lookupStruct = Map.lookup name . delta_structs . sortEnv_delta in
        asks lookupStruct >>= \case
          Just flds | Just ty <- lookup f flds -> pure (rtypeToSort ty)
          _ -> empty
    SortArray _ _ | f == "length" -> pure (SortInt (Just 256))
    _ -> empty
  PFieldUpd e f ef -> do
    se <- predSort e
    sf <- predSort ef
    case se of
      SortStruct name ->
        let lookupStruct = Map.lookup name . delta_structs . sortEnv_delta in
          asks lookupStruct >>= \case
            Just flds
              | Just (rtypeToSort -> sf2) <- lookup f flds
              , sf == sf2 -> pure se
            _ -> empty
      SortArray _ _ | f == "length", SortInt _ <- sf -> pure se
      _ -> empty
  PUnintFn n es -> case n of
    "sum" | [e] <- es -> predSort e >>= \case
                SortArray SortInt{} _ -> pure (SortInt Nothing)
                SortMapping _ SortInt{} -> pure (SortInt Nothing)
                _ -> empty
    "nnz" | [e] <- es -> predSort e >>= \case
                SortMapping _ SortInt{} -> pure (SortInt Nothing)
                _ -> empty
    "flatten" | [e] <- es -> predSort e >>= \case
                  SortMapping tk (SortMapping _ tv) -> pure (SortMapping tk tv)
                  _ -> empty
    "fld"
      | [PVar name, PVar f, e] <- es -> do
          flds <- liftAsks (Map.lookup name . delta_structs . sortEnv_delta)
          RType _ fldTy _ <- SortCheckT . lift . MaybeT . pure $ Map.lookup f (Map.fromList flds)
          let fldSort = skelToSort fldTy
          predSort e >>= \case
            SortMapping tk (SortStruct n2) | n2 == name -> pure (SortMapping tk fldSort)
            _ -> empty
    "sumTo" | [ea, ei] <- es -> do
                predSort ea >>= \case
                  SortArray SortInt{} _ -> pure ()
                  _ -> empty
                let isSortInt = \case
                      SortInt{} -> True
                      _ -> False
                unlessM (isSortInt <$> predSort ei) empty
                pure (SortInt Nothing)
    _ -> empty
  PHavoc ty -> pure (skelToSort ty)
  PCast e ty -> do
    _ <- predSort e
    let sTo = skelToSort ty
    pure sTo
  where
    twoBoolSort p q = do
      sp <- predSort p
      sq <- predSort q
      if sp == SortBool && sq == SortBool then pure SortBool else empty

evalSortCheckT :: SortCheckT m a -> SortEnv -> m (Maybe a)
evalSortCheckT m env
  = runMaybeT
  . flip runReaderT env
  . runSortCheckT
  $ m

evalSortCheck :: SortCheck a -> SortEnv -> Maybe a
evalSortCheck m env = runIdentity (evalSortCheckT m env)

exprSort :: Expr -> SortCheck Sort
exprSort = predSort . exprToPred

tcEnvToSortEnv :: LocalEnv a -> Delta () -> SortEnv
tcEnvToSortEnv env delta =
  SortEnv { sortEnv_vars = Map.map rtypeToSort (localEnvVars env)
          , sortEnv_delta = delta }

-- | Get sort of expression, if well-sorted.
getExprSort :: Expr -> SortEnv -> Maybe Sort
getExprSort e = evalSortCheck (exprSort e)

-- | Check well-sortedness of predicate. If well-sorted, should return
-- [SortBool].

getPredSort :: Pred -> SortEnv -> Maybe Sort
getPredSort p = evalSortCheck (predSort p)
