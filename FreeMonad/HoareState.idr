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

hrun : s >< p -> HoareState s a p q -> (a, s)
hrun i (HS st) =
  case st i of
   (x ** _) => x

hget : HoareState s s (\_ => Unit) (\s1, (x, s2) => (x = s1, s2 = s1))
hget = HS $
  \(s ** _) =>
    ((s, s) ** (Refl, Refl))

modify : (f : s -> s) -> HoareState s () (\_ => Unit) (\s1, (_, s2) => (f s1) = s2)
modify f = HS $
  \(s ** _) => (((), f s) ** Refl)

hput : (x : s) -> HoareState s () (\_ => Unit) (\_, (_, s2) => s2 = x)
hput x = HS $
  \_ => (((), x) ** Refl)
