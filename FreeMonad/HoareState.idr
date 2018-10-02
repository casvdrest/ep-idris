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

infixr 4 ===>

data (===>) a b =
    Implies (a -> b)

||| Predicate atoms
data Atom s = Access Path FMod
            | Exists Path
            | HasType Path
            | StateEq s

||| Equality for predicate atoms
implementation Eq s => Eq (Atom s) where
  (Access p m) == (Access p' m') = p == p' && m == m'
  (Exists p) == (Exists p') = p == p'
  (HasType p) == (HasType p') = p == p'
  (StateEq s) == (StateEq s') = s == s'
  _ == _ = False

infix 1 ><

(><) : (a : Type) -> (a -> Type) -> Type
a >< b = DPair a b

Pre : Type -> Type
Pre s = s -> Type

Post : Type -> Type -> Type
Post s a = s -> (a, s) -> Type

data HoareState : (s : Type) -> (a : Type) -> Pre s -> Post s a -> Type where
  HS : ((prf : (s >< p)) -> (a, s) >< q (fst prf)) -> HoareState s a p q

hreturn : (Eq s, Eq a) => (y : a) -> HoareState s a (\s => Unit) (\i, (x, f) => (x = y, i = f))
hreturn y = HS $
  \(s ** _) =>
    ((y, s) ** (Refl, Refl)
  )

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
