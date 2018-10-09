module Main

import Free
import HoareState
import Environment

import Data.Vect
import Data.So

%access export

data Except a = Result a
              | E String
              
implementation Functor Except where 
  map f (Result a) = Result (f a)
  map f (E msg   ) = E msg
  
implementation Applicative Except where 
  pure = Result
  (Result f) <*> g = map f g
  (E msg   ) <*> g = E msg
  
implementation Monad Except where 
  (Result x) >>= g = g x
  (E msg   ) >>= _ = E msg
  
implementation (Show a) => Show (Except a) where 
  show (Result x) = "(Result " ++ show x ++ ")"
  show (E str   ) = "(Error " ++ str ++ ")"

getFS : IO FSTree
getFS = pure $ FSLeaf (MkFileInfo "file.txt" 
    (MkFileMD F [[True, True, True], [True, True, True], [True, True, True]] (U "cas" "root"))
  )
  
error : Except a 
error = E "Error thrown" 

predToPrf : (p : Predicate) -> Except (asType p)
predToPrf (x /\ y) = pure (!(predToPrf x), !(predToPrf y))
predToPrf (x :=> y) = do 
  x' <- predToPrf x
  y' <- predToPrf y 
  pure (const y')
predToPrf (x =:= y) = 
  case decEq x y of 
    (Yes prf) => pure prf
    (No _   ) => error
predToPrf T = pure ()
predToPrf F = error

execP : (x : Int) -> {p : Pre' Int} 
                  -> {q : Post' Int a} 
                  -> HoareStateP Int a p q 
                  -> Except ((a, Int) >< [[..]] q x)
execP init {p} {q} st = do
  prf <- predToPrf (p init) 
  pure (hrunP (init ** prf) st)

hget10 : HoareStateP Int Int (\s => s =:= 10) (\s1, (x, s2) => s1 =:= s2 /\ s2 =:= x)
hget10 = HSP $ \(s ** _) => ((s, s) ** (Refl, Refl))

hgetI : HoareStateP Int Int (\s => T) (\s1, (x, s2) => s1 =:= s2 /\ s2 =:= x)
hgetI = HSP $ \(s ** _) => ((s, s) ** (Refl, Refl))

hputI : (x : Int) -> HoareStateP Int () (\s => T) (\s1, (_, s2) => s2 =:= x)
hputI x = HSP $ \(s ** _) => (((), x) ** Refl) 

prog : Except (Int, Int)
prog = fst `map` (execP 10 hget10)

main : IO () 
main = do 
  let x = prog 
  print x
 
 
