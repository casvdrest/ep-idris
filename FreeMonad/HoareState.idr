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

||| Models a state predicate as an expression Tree
data Predicate : (s : Type) -> Type where
  Top : Predicate s
  Bottom : Predicate s
  (:&&:) : Predicate s -> Predicate s -> Predicate s
  (:||:) : Predicate s -> Predicate s -> Predicate s
  (:=>:) : Predicate s -> Predicate s -> Predicate s
  Not : Predicate s -> Predicate s
  -- The 'Defer' constructor indicates that the contained predicate
  -- should not be evaluated on the current state, but rather on the
  -- next state.
  Defer : Predicate s -> Predicate s

infixr 1 <>

(<>) : String -> String -> String
xs <> ys = xs ++ ys

implementation Show (Predicate s) where
  show Top = "T"
  show Bottom = "B"
  show (a :&&: b) = "(" <> show a <> " && " <> show b <> ")"
  show (a :||: b) = "(" <> show a <> " || " <> show b <> ")"
  show (a :=>: b) = "(" <> show a <> " => " <> show b <> ")"
  show (Defer s) = "(Defer " <> show s <> ")"

||| Captures failure
data Except a = Error String | Result a

||| Throws an error (i.e. lift an error message into the Except data type)
throw : String -> Except a
throw = Error

||| Throws an error that indicates that assertion of the provided
||| predicate failed
pfail : Predicate s -> Except a
pfail p = Error $ "Assertion of the state predicate " <> show p <> " returned False"

||| Asserts the validity of a predicate. Deferred branches are considered to
||| hold on the current state.
|||
||| Furthermore, a predicate is returned containing those parts of the tree
||| that were not evaluated during this pass
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

||| Equivalent to StateT Except, though the HoareState data type is decorated
||| with a pre- and postcondition.
|||
||| these predicates are statically composed at compile-time, but only checked
||| dynamically. The reason for this is that the validity of a predicate may
||| rely on the changes made to the shared mutable state (e.g. the file system)
||| by other parts of the program, meaning that statically checking all
||| predicates is not possible.
data HoareState : (s : Type) -> Predicate s -> Predicate s -> (a : Type) -> Type where
 HS : (Predicate s -> s -> HVect [s, Except a, Predicate s]) -> HoareState s p q a

||| Lift a value into the HoareState context
hreturn : Eq s => a -> HoareState s Top (Defer Top) a
hreturn x = HS $
  \p, s =>
    case check p s of
      (True, rp) => [s, Result x, rp]
      (False, _) => [s, pfail p, Bottom]

||| Compose two computations in the HoareState context. (Largely) isomorphic
||| to the monadic bind (>>=)
hbind : Eq s => HoareState s p1 q1 a -> (a -> HoareState s p2 q2 b) ->
                HoareState s
                  (p1 :&&: (Defer q1) :=>: (Defer p2))
                  ((Defer q1) :&&: (Defer $ Defer q2)) b
hbind (HS st) f = HS $
  \p, s =>
    case check p s of
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
                  (False, _)   => [s'', pfail (rem' :&&: rp'), Bottom]
              (Error str) => [s', Error str, Bottom]
          (False, rp') =>
            [s', pfail (rem :&&: rp), Bottom]
      (False, _) => [s, pfail p, Bottom]

||| Get the current state value stored in a HoareState context
hget : Eq s => HoareState s Top (Defer Top) s
hget = HS $
  \p, s =>
    case check p s of
      (True, rp) => [s, Result s, rp]
      (False, _) => [s, pfail p, Bottom]

||| Replace the current state value stored in a HoareState context
hput : Eq s => (x : s) -> HoareState s Top Top ()
hput s' = HS $
  \p, s =>
    case check p s of
      (True, rp) => [s', Result (), rp]
      (False, _) => [s', pfail p, Bottom]

||| Evaluate a computation in the HoareState context to it's resulting
||| value and state
hrun : (Show s) => {p : Predicate s} -> {q : Predicate s} -> HoareState s p q a -> s -> (s, Except a)
hrun {p} {q} (HS st) s =
  case check (p :&&: q) s of
    (True, rp) =>
      let [s', x, rp'] =
        st rp s in
      (s', x)
    (False, _) => (s, pfail (p :&&: q))

infixl 1 >>=

||| Idris allows for rebinding do notation by syntactically overloading the '>>=' operator.
||| I utilize this to forgo the trouble of defining Functor/Applicative/Monad
||| instances for the HoareState data type.
(>>=) : Eq s => HoareState s p1 q1 a -> (a -> HoareState s p2 q2 b) ->
                HoareState s
                  (p1 :&&: (Defer q1) :=>: (Defer p2))
                  ((Defer q1) :&&: (Defer $ Defer q2)) b
(>>=) = hbind

||| Example program 
iget : HoareState Int
  (Top :&&: Defer Top :=>: Defer (Top :&&: Defer (Defer Top) :=>: Defer (Top :&&: Defer (Defer Top) :=>: Defer Top)))
  (Defer Top :&&: Defer (Defer (Defer (Defer Top) :&&: Defer (Defer (Defer (Defer Top) :&&: Defer (Defer (Defer Top))))))) Int
iget = do
  hput 100
  x <- hget
  v <- hreturn x
  hreturn v
