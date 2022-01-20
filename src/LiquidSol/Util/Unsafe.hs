module LiquidSol.Util.Unsafe where

import Prelude hiding (head)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Hashable (Hashable)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import GHC.Stack (HasCallStack)

-- | Version of Map.! with better stack trace
unsafeLookup :: HasCallStack => Ord a => Map a b -> a -> b
unsafeLookup m k = case Map.lookup k m of
  Just v -> v
  Nothing -> error "given key is not an element in the map"

-- | Version of HashMap.! with better stack trace
hmUnsafeLookup :: (HasCallStack, Ord a, Hashable a) => HashMap a b -> a -> b
hmUnsafeLookup m k = case HashMap.lookup k m of
  Just v -> v
  Nothing -> error "given key is not an element in the map"

fromJust :: HasCallStack => Maybe a -> a
fromJust = \case
  Just x -> x
  Nothing -> error "fromJust: Nothing"

head :: HasCallStack => [a] -> a
head xs = case xs of
  [] -> error "empty list"
  (x:_) -> x
