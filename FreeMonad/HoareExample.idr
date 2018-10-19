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

hgetFS : HoareStateP FSTree FSTree (\s => T) (\(x, s2) => s2 =:= x)
hgetFS = HSP $ \(s ** _) => ((s, s) ** Refl)

hputFS : (x : FSTree) -> HoareStateP FSTree () (\s => T) (\(_, s2) => s2 =:= x)
hputFS x = HSP $ \(s ** _) => (((), x) ** Refl)

Data Pred : Type -> Type where 
	

data Cmd = 
	Ls   FilePath ([FilePath] -> Cmd)
	Echo String (String -> Cmd)
	Cat  FilePath (String -> Cmd)

pre : Cmd -> Predicate a 
pre (LS path)