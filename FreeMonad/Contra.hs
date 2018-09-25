module Contra where

class Functor f where
  fmap : (a -> b) -> f a -> f a

class Contravariant f where
  comap : (b -> a) -> f a -> f b

type Reader a = String -> a

instance Functor Reader where
  fmap f r = r . f