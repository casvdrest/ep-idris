module Main

import Control.Monad.State
import Data.HVect
import Environment
import Data.So

prefix 6 :!
infixl 5 :&&:
infixl 4 :||:
infixl 3 :=>:

%hide (>>=)

data Except a = Error String | Result a

throw : String -> Except a
throw = Error

data Predicate : (s : Type) -> Type where
  Top : Predicate s
  Bottom : Predicate s
  (:&&:) : Predicate s -> Predicate s -> Predicate s
  (:||:) : Predicate s -> Predicate s -> Predicate s
  (:=>:) : Predicate s -> Predicate s -> Predicate s
  Not : Predicate s -> Predicate s
  Defer : Predicate s -> Predicate s

infixr 1 <>

(<>) : String -> String -> String
xs <> ys = xs ++ ys

implementation (Show s) => Show (Predicate s) where
  show Top = "T"
  show (a :&&: b) = "(" <> show a <> " && " <> show b <> ")"
  show (a :||: b) = "(" <> show a <> " || " <> show b <> ")"
  show (a :=>: b) = "(" <> show a <> " => " <> show b <> ")"
  show (Defer s) = "(Defer " <> show s <> ")"

check : Predicate s -> s -> (Bool, Predicate s)
check (Defer p)  _ = (True, p)
check Top        _ = (False, Top)
check Bottom     _ = (False, Bottom)
check (p :&&: q) s =
  let (x1, r1) =
    check p s in
  let (x2, r2) =
    check q s in
  let rp =
    r1 :&&: r2 in
  (x1 && x2, rp)
check (p :||: q) s =
  let (x1, r1) =
    check p s in
  let (x2, r2) =
    check q s in
  let rp =
    r1 :||: r2 in
  (x1 || x2, rp)
check (p :=>: q) s = check ((Not p) :||: q) s
check (Not p) s = let (r, pr) = check p s in (not r, pr)


data HoareState : (s : Type) -> Predicate s -> Predicate s -> (a : Type) -> Type where
 HS : (Predicate s -> s -> HVect [s, Except a, Predicate s]) -> HoareState s p q a

hreturn : Eq s => a -> HoareState s Top (Defer Top) a
hreturn x = HS $
  \p, s =>
    case check p s of
      (True, rp) => [s, Result x, rp]
      (False, _) => [s, throw "Error", Bottom]


hbind : Eq s => HoareState s p1 q1 a -> (a -> HoareState s p2 q2 b) ->
                HoareState s
                  (p1 :&&: (Defer q1) :=>: (Defer p2))
                  ((Defer q1) :&&: (Defer $ Defer q2)) b
hbind (HS st) f = HS $
  \pre, s =>
    case check pre s of
      (True, rp) =>
        let [s', x, rem] =
          st rp s in
        case check (rem :&&: rp) s' of
          (True, rp') =>
            case x of
              (Result v) =>
                let HS st' =
                  (f v) in
                let [s'', x', rem'] =
                  st' rp' s' in
                case check (rem' :&&: rp') s' of
                  (True, rp'') => [s'', x', rp'' :&&: rem']
                  (False, _)   => [s'', throw "Error", Bottom]
              (Error str) => [s', Error str, Bottom]
          (False, rp') =>
            [s', throw "Error", Bottom]
      (False, _) => [s, throw "Error", Bottom]

hget : Eq s => HoareState s Top (Defer Top) s
hget = HS $
  \p, s =>
    case check p s of
      (True, rp) => [s, Result s, rp]
      (False, _) => [s, throw "Error", Bottom]

hput : Eq s => (x : s) -> HoareState s Top Top ()
hput s' = HS $
  \p, s =>
    case check p s of
      (True, rp) => [s', Result (), rp]
      (False, _) => [s', throw "Error", Bottom]


hrun : (Show s) => {p : Predicate s} -> {q : Predicate s} -> HoareState s p q a -> s -> (s, Except a)
hrun {p} {q} (HS st) s =
  case check (p :&&: q) s of
    (True, rp) =>
      let [s', x, rp'] =
        st rp s in
      (s', x)
    (False, _) => (s, throw "Precondition failed")

infixl 1 >>=

(>>=) : Eq s => HoareState s p1 q1 a -> (a -> HoareState s p2 q2 b) ->
                HoareState s
                  (p1 :&&: (Defer q1) :=>: (Defer p2))
                  ((Defer q1) :&&: (Defer $ Defer q2)) b
(>>=) = hbind

iget : HoareState Int
  (Top :&&: Defer Top :=>: Defer (Top :&&: Defer (Defer Top) :=>: Defer (Top :&&: Defer (Defer Top) :=>: Defer Top)))
  (Defer Top :&&: Defer (Defer (Defer (Defer Top) :&&: Defer (Defer (Defer (Defer Top) :&&: Defer (Defer (Defer Top))))))) Int
iget = do
  hput 100
  x <- hget
  v <- hreturn x
  hreturn v
