module Contra where

class Functor f where
  fmap : (a -> b) -> f a -> f a

class Contravariant f where
  comap : (b -> a) -> f a -> f b

type Reader a = String -> a

type Shower a = a -> Bool

instance Functor Reader where
  fmap f r = (\s -> f (r s))

instance Contravariant Shower where
  comap f p = (\v -> p (f v))
