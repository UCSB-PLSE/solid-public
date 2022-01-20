{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
module LiquidSol.LiOpts
  ( LiOpts(..), defaultLiOpts
  , OptsT, runOptsT
  , MonadOpts(..))where

import Control.Monad.Except (MonadError)
import Control.Monad.Reader

data LiOpts = LiOpts
  { logSolve :: Bool
  , logSmt :: Bool
  , logInitialAssign :: Bool
  , logDir :: Maybe FilePath
  , smtTimeout :: Int
  , totalTimeout :: Maybe Int
  , z3Path :: String
  }
  deriving (Show)

defaultLiOpts :: LiOpts
defaultLiOpts = LiOpts
  { logSolve = False
  , logSmt = False
  , logInitialAssign = False
  , logDir = Nothing
  , smtTimeout = 1000
  , totalTimeout = Nothing
  , z3Path = "z3"
  }

newtype OptsT m a = OptsM { unOptsM :: ReaderT LiOpts m a }
  deriving ( Functor, Applicative, Monad, MonadTrans, MonadIO
           , MonadError e)

runOptsT :: LiOpts -> OptsT m a -> m a
runOptsT opts m = runReaderT (unOptsM m) opts

class Monad m => MonadOpts m where
  getOpts :: m LiOpts

instance Monad m => MonadOpts (OptsT m) where
  getOpts = OptsM ask
