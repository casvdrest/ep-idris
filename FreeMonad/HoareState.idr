module HoareState

import Control.Monad.State
import Data.HVect
import Environment
import Data.So

prefix 6 :!
infixl 5 :&&:
infixl 4 :||:
infixl 3 :=>:

%access public export
%language ElabReflection

infix 1 ><

||| Constructs a dependent pair
(><) : (a : Type) -> (a -> Type) -> Type
a >< b = DPair a b

||| pre condition
Pre : Type -> Type
Pre s = s -> Type

||| post-condition
Post : Type -> Type -> Type
Post s a = s -> (a, s) -> Type

infixl 5 /\
infixl 4 :=>
infix  6 =:=

data Predicate : Type where 
  (/\)  : Predicate -> Predicate -> Predicate 
  (:=>) : Predicate -> Predicate -> Predicate 
  (=:=) : DecEq s => s -> s -> Predicate 
  T : Predicate 
  F : Predicate 
  
total
Pre' : Type -> Type 
Pre' s = s -> Predicate 

total
Post' : Type -> Type -> Type 
Post' s a = s -> (a, s) -> Predicate

total
asType : Predicate -> Type 
asType (p /\  q) = (asType p, asType q)
asType (p :=> q) = asType p -> asType q
asType (a =:= b) = a = b
asType T          = Unit 
asType F          = Void

syntax "[[..]]" [pred] = HoareState.asType . pred

||| State monad with pre- and post condition
data HoareState : (s : Type) -> (a : Type) -> Pre s -> Post s a -> Type where
  HS  : ((prf : (s >< p)) -> (a, s) >< q (fst prf)) -> HoareState s a p q 

data HoareStateP : (s : Type) -> (a : Type) -> Pre' s -> Post' s a -> Type where 
  HSP : ((prf : (s >< [[..]] p)) -> (a, s) >< [[..]] q (fst prf)) -> HoareStateP s a p q 
  
data HoareStateI : (a : Type) -> Pre' Int -> Post' Int a -> Type where 
  HSI : ((prf : (Int >< [[..]] p)) -> (a, Int) >< [[..]] q (fst prf)) -> HoareStateI a p (assert_total q)
  
hgetP : (DecEq s, DecEq a) => HoareStateP s s (\s => T) (\s1, (a, s2) => s1 =:= s2 /\ s2 =:= a)
hgetP = HSP $
  \(s ** _) =>
    ((s, s) ** (Refl, Refl))
    
hreturnP : (DecEq s, DecEq a) => (x : a) -> HoareStateP s a (\_ => T) (\s1, (y, s2) => s1 =:= s2 /\ x =:= y)
hreturnP y = HSP $
  \(s ** _) =>
    ((y, s) ** (Refl, Refl)
  )
  
hrunP : (prf : s >< [[..]] p) -> HoareStateP s a p q -> ((a, s) >< [[..]] q (fst prf))
hrunP prf (HSP st) = st prf
  
||| Lift a value into the HoareState context
hreturn : (Eq s, Eq a) => (y : a) -> HoareState s a (\s => Unit) (\i, (x, f) => (x = y, i = f))
hreturn y = HS $
  \(s ** _) =>
    ((y, s) ** (Refl, Refl)
  )

||| Sequencing of HoareState
hbind : {a : Type} -> {b : Type} -> {s : Type}
                   -> {p1 : Pre s} -> {q1 : Post s a}
                   -> {p2 : a -> Pre s} -> {q2 : a -> Post s b}
                   -> HoareState s a p1 q1
                   -> ((x : a) -> HoareState s b (p2 x) (q2 x))
                   -> HoareState s b
                        (\s1 =>
                          (p1 s1, ((x : a) -> (s2 : s) -> q1 s1 (x, s2) -> p2 x s2))
                        )
                        (\s1, (x, s3) =>
                          ((a, s) >< (\(y, s2) => (q1 s1 (y,s2), q2 y s2 (x, s3))))
                        )
hbind (HS f) g = HS $ \(s1 ** pre) =>
  case f (s1 ** (fst pre)) of
    ((x, s2) ** p) =>
      let HS g' = g x in
      case g' (s2 ** ((snd pre) x s2 p)) of
        ((y, s3) ** q) => ((y, s3) ** ((x, s2) ** (p, q)))

||| Compute a value from a HoareState
hrun : (prf : s >< p) -> HoareState s a p q -> ((a, s) >< (q (fst prf)))
hrun i (HS st) = st i

||| Retrieve the current state value in a HoareState
hget : {s : Type} -> HoareState s s (\_ => Unit) (\s1, (a, s2) => (s1 = s2, s2 = a))
hget = HS $
  \(s ** _) =>
    ((s, s) ** (Refl, Refl))

||| Use the given function to modify the current state
modify : (f : s -> s) -> HoareState s () (\s => Unit) (\s1, (a, s2) => (f s1) = s2)
modify f = HS $
  \(s ** _) => (((), f s) ** Refl)

||| Exchange the current state with the input value
hput : (x : s) -> HoareState s () (\_ => Unit) (\_, (_, s2) => s2 = x)
hput x = HS $
  \_ => (((), x) ** Refl)
  
||| Increment the current state value with the given amount
increment : Num a => (n : a) -> HoareState a () (\_ => Unit) (\s1, (_, s2) => (s1 + n) = s2)
increment n = HS $ 
  \(s ** _) => (((), s + n) ** Refl)
