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
  Forall : {s : Type} -> (s -> Predicate) -> Predicate
  T : Predicate 
  F : Predicate 
  
total
Pre' : Type -> Type 
Pre' s = s -> Predicate 

total
Post' : Type -> Type -> Type 
Post' s a = (a, s) -> Predicate

total
asType : Predicate -> Type 
asType (p /\  q)  = (asType p, asType q)
asType (p :=> q)  = asType p -> asType q
asType (a =:= b)  = a = b
asType (Forall {s} p) = (x : s) -> asType (p x)
asType T          = Unit 
asType F          = Void

syntax "[[..]]" [pred] = HoareState.asType . pred
syntax "fa." [f] = Forall f
syntax "faT." [ty] [f] = Forall {s = ty} f

||| State monad with pre- and post condition
data HoareState : (s : Type) -> (a : Type) -> Pre s -> Post s a -> Type where
	HS  : ((prf : (s >< p)) -> (a, s) >< q (fst prf)) -> HoareState s a p q 
	
||| State monad with pre- and post condition
data HoareStateP : (s : Type) -> (a : Type) -> Pre' s -> Post' s a -> Type where
  HSP  : ((prf : (s >< [[..]] p)) -> (a, s) >< [[..]] q) -> HoareStateP s a p q 
          
hbindI : {a : Type} -> {b : Type}
                    -> {auto p1 : Pre' Int} -> {auto q1 : Post' Int a}
                    -> {auto p2 : a -> Pre' Int} -> {auto q2 : Post' Int b}
                    -> HoareStateP Int a p1 q1
                    -> ((x : a) -> HoareStateP Int b (p2 x) q2)
                    -> HoareStateP Int b
                         (\s1 => 
                           p1 s1 /\ (fa. (\x => fa. (\s2 => q1 (x, s2) :=> p2 x s2 )))
                         ) (\(x, s3) => q2 (x, s3))
hbindI (HSP st) g = HSP $ 
  \(s1 ** (l, r)) => 
    case st (s1 ** l) of 
      ((x, s2) ** p) => 
        let HSP g' 
          = g x in 
        case g' (s2 ** (r x s2 p)) of 
          ((y, s3) ** q) => ((y, s3) ** q)

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
      let HS g' 
        = g x in
      case g' (s2 ** ((snd pre) x s2 p)) of
        ((y, s3) ** q) => ((y, s3) ** ((x, s2) ** (p, q)))

||| Compute a value from a HoareState
hrun : (prf : s >< p) -> HoareState s a p q -> ((a, s) >< (q (fst prf)))
hrun i (HS st) = st i

hrunP : (prf : s >< [[..]] p) -> HoareStateP s a p q -> ((a, s) >< [[..]] q)
hrunP i (HSP st) = st i

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
 
str : {a : Type} -> {s : Type}
                 -> {q : Post s a}
                 -> {p1 : Pre s} -> {p2 : Pre s}
                 -> ((i : s) -> p2 i -> p1 i)
                 -> HoareState s a p1 q
                 -> HoareState s a p2 q 
str f (HS st) = HS $ 
  \(i ** p) => st (i ** (f i p))
  
wkn : {a : Type} -> {s : Type} 
                 -> {p : Pre s}
                 -> {q1 : Post s a} -> {q2 : Post s a}
                 -> ((s1 : s) -> (x : a) -> (s2 : s) -> p s1 -> q1 s1 (x, s2) -> q2 s1 (x, s2))
                 -> HoareState s a p q1
                 -> HoareState s a p q2 
wkn g (HS st) = HS $ 
  \(s1 ** p) => 
    case st (s1 ** p) of 
      ((x, s2) ** q) => ((x, s2) ** g s1 x s2 p q)

rwr : {a : Type} -> {s : Type} 
                 -> {p1 : Pre s} -> {q1 : Post s a} 
                 -> {p2 : Pre s} -> {q2 : Post s a} 
                 -> ((i : s) -> p2 i -> p1 i) 
                 -> ((i : s) -> (x : a) -> (f : s) -> p2 i -> q1 i (x, f) -> q2 i (x, f))
                 -> HoareState s a p1 q1 
                 -> HoareState s a p2 q2 
rwr f g = wkn g . str f 
 
strFS : {a : Type} -> {q : Post' FSTree a}
									-> {p1 : Pre' FSTree} -> {p2 : Pre' FSTree}
									-> ((i : FSTree) -> ([[..]] p2) i
																-> ([[..]] p1) i)
									-> HoareStateP FSTree a p1 q 
									-> HoareStateP FSTree a p2 q
strFS f (HSP st) = HSP $ 
	\(i ** p) => 
		st (i ** (f i p))

wknFS : {a : Type} -> {p : Pre' FSTree} 
									-> {q1 : Post' FSTree a} -> {q2 : Post' FSTree a}
									-> ((i : FSTree) -> (x : a) -> (f : FSTree)
																-> ([[..]] p) i 
																-> ([[..]] q1) (x, f)
																-> ([[..]] q2) (x, f))
									-> HoareStateP FSTree a p q1
									-> HoareStateP FSTree a p q2 
wknFS g (HSP st) = HSP $ 
	\(s1 ** p) => 
		case st (s1 ** p) of 
			((x, s2) ** q) => ((x, s2) ** g s1 x s2 p q)

rwrFS : {a : Type} -> {Int : Type} 
									-> {p1 : Pre' FSTree} -> {q1 : Post' FSTree a} 
									-> {p2 : Pre' FSTree} -> {q2 : Post' FSTree a} 
									-> ((i : FSTree) -> ([[..]] p2) i 
															  -> ([[..]] p1) i) 
									-> ((i : FSTree) -> (x : a) -> (f : FSTree) 
															-> ([[..]] p2) i 
															-> ([[..]] q1) (x, f) 
															-> ([[..]] q2) (x, f))
									-> HoareStateP FSTree a p1 q1 
									-> HoareStateP FSTree a p2 q2
rwrFS f g = wknFS g . strFS f   