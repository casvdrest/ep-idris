module Test where

class (Functor f) => Eval f where 
    algebra :: (f a) -> a