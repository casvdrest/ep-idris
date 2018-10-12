module Main

import Free
import HoareState
import Environment

import Data.Vect
import Data.So

%access export

Except : Type -> Type 
Except = Either String

getFS : IO FSTree
getFS = pure $ FSLeaf (MkFileInfo "file.txt" 
    (MkFileMD F [[True, True, True], [True, True, True], [True, True, True]] (U "cas" "root"))
  )
  
err : Except a 
err = Left "Error thrown" 

predToPrf : (p : Predicate) -> Except (asType p)
predToPrf (x /\ y) = pure (!(predToPrf x), !(predToPrf y))
predToPrf (x :=> y) = do 
  x' <- predToPrf x
  y' <- predToPrf y 
  pure (const y')
predToPrf (x =:= y) = 
  case decEq x y of 
    (Yes prf) => pure prf
    (No _   ) => err
predToPrf T = pure () 
predToPrf F = err
-- No total definition exists for this case (a -> m b -> m (a -> b) cannot be defined)
predToPrf (Forall f) = pure $ (\s => (\(Right x) => x) (predToPrf (f s)))
predToPrf (Exists f) = 
  let x = 
    ?val_x in 
  case predToPrf (f x) of
    (Right y) => pure (x ** y)
    (Left  e) => err

-- Temporarily use Int as hardcoded state type, as instantiating polymorphic hoare states
-- still yields some problems. 
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

program : HoareState Int Int p (\_, _ => Unit)
program = wkn ?f $ 
  hputI 10 `hbind` (\_ => 
  hgetI
  )

-- This will generate a dynamic error, since the precondition of hget10 requires 
-- the state to be equal to '10'
prog : Except (Int, Int)
prog = fst `map` (execP 11 hget10)

main : IO ()
main = do
  let x = prog 
  print x
