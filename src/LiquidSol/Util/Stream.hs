module LiquidSol.Util.Stream where

import Prelude hiding (take, repeat, head, tail)

data Stream a = SCons a (Stream a)
  deriving (Show, Eq, Ord, Functor)

take :: Int -> Stream a -> ([a], Stream a)
take n (SCons x ss) =
  let (xs, ss') = take (n - 1) ss in
    (x : xs, ss')

head :: Stream a -> a
head (SCons x _) = x

tail :: Stream a -> Stream a
tail (SCons _ xs) = xs

repeat :: a -> Stream a
repeat x = SCons x (repeat x)

extract :: Stream a -> (a, Stream a)
extract (SCons x ss) = (x, ss)

unfold :: (a -> a) -> a -> Stream a
unfold f x0 = SCons x0 (unfold f (f x0))
