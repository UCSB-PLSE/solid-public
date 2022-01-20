module LiquidSol.Util.Fresh where

import LiquidSol.Util.Stream (Stream)
import qualified LiquidSol.Util.Stream as Stream

import Data.Functor.Identity
import Control.Monad.State.Strict

newtype FreshT s m a = FreshT { runFreshT :: StateT (Stream s) m a }
  deriving ( Functor, Applicative, Monad, MonadTrans )

type Fresh s = FreshT s Identity

evalFreshT :: Monad m => Stream s -> FreshT s m a -> m a
evalFreshT s m = fmap fst . runStateT (runFreshT m) $ s

nextFresh :: Monad m => FreshT s m s
nextFresh = FreshT $ do
  current <- gets Stream.head
  modify Stream.tail
  pure current
