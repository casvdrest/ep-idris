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

||| Predicate atoms
data Atom = Access Path FMod
          | Exists Path
          | HasType Path

||| Equality for predicate atoms
implementation Eq Atom where
  (Access p m) == (Access p' m') = p == p' && m == m'
  (Exists p) == (Exists p') = p == p'
  (HasType p) == (HasType p') = p == p'
  _ == _ = False

||| Interface for monads that are able to assert atomic predicates
||| Typically, the IO monad is used for this, but by making the
||| computation context parameterizable, another context can be used
||| for testing purposes
interface Monad m => AssertAtomic (s : Type) (m : Type -> Type) where
  total assertAtom : Atom -> s -> m Bool

||| Models a state predicate as an expression Tree
data Predicate : (s : Type) -> Type where
  -- Top/true -> predicate that is always true
  Top : Predicate s

  -- Bottom/false -> predicate that is always false
  Bottom : Predicate s

  -- Boolean conjunction
  (:&&:) : Predicate s -> Predicate s -> Predicate s

  -- Boolean disjunction
  (:||:) : Predicate s -> Predicate s -> Predicate s

  -- Boolean implication
  (:=>:) : Predicate s -> Predicate s -> Predicate s

  -- Negates the value of its input predicate
  Not : Predicate s -> Predicate s

  -- Indicates an atomic predicate
  At : Atom -> Predicate s

  -- The 'Df' (Df) constructor indicates that the contained predicate
  -- should not be evaluated on the current state, but rather on the
  -- next state.
  Df : Predicate s -> Predicate s

infixr 1 <>

(<>) : String -> String -> String
xs <> ys = xs ++ ys

implementation Show (Predicate s) where
  show Top = "T"
  show Bottom = "B"
  show (a :&&: b) = "(" <> show a <> " && " <> show b <> ")"
  show (a :||: b) = "(" <> show a <> " || " <> show b <> ")"
  show (a :=>: b) = "(" <> show a <> " => " <> show b <> ")"
  show (Df s) = "(Df " <> show s <> ")"

||| Captures failure
data Except a = Error String | Result a

||| Throws an error (i.e. lift an error message into the Except data type)
throw : String -> Except a
throw = Error

||| Throws an error that indicates that assertion of the provided
||| predicate failed
pfail : Predicate s -> Except a
pfail p = Error $ "Assertion of the state predicate " <> show p <> " returned False"

||| Asserts the validity of a predicate. Dfred branches are considered to
||| hold on the current state.
|||
||| Furthermore, a predicate is returned containing those parts of the tree
||| that were not evaluated during this pass
|||
||| !! TODO !! don't return Top if there is no predicate to return!
check : AssertAtomic s m => Predicate s -> s -> m (Bool, Predicate s)
check (Df p)  _ = pure (True, p)
check Top        _ = pure (True, Top)
check Bottom     _ = pure (False, Bottom)
check (p :&&: q) s = do
  (x1, rp1) <- check p s
  (x2, rp2) <- check q s
  pure (x1 && x2, rp1 :&&: rp2)
check (p :||: q) s = do
  (x1, rp1) <- check p s
  (x2, rp2) <- check q s
  pure (x1 || x2, rp1 :||: rp2)
check (p :=>: q) s = check ((Not p) :||: q) s
check (Not p) s = do
  (r, pr) <- check p s
  pure (not r, pr)
check (At a) s = pure (!(assertAtom a s), Top)

||| Equivalent to StateT Except, though the HoareState data type is decorated
||| with a pre- and postcondition.
|||
||| these predicates are statically composed at compile-time, but only checked
||| dynamically. The reason for this is that the validity of a predicate may
||| rely on the changes made to the shared mutable state (e.g. the file system)
||| by other parts of the program, meaning that statically checking all
||| predicates is not possible.
data HoareState : (s : Type) -> (m : Type -> Type) -> Predicate s -> Predicate s -> (a : Type) -> Type where
 HS : (AssertAtomic s m) => (Predicate s -> s -> m (HVect [s, Except a, Predicate s])) -> HoareState s m p q a

||| Lift a value into the HoareState context
hreturn : (AssertAtomic s m) => a -> HoareState s m Top (Df Top) a
hreturn x = HS $
  \p, s =>
    case !(check p s) of
      (True, rp) => pure [s, Result x, rp]
      (False, _) => pure [s, pfail p, Bottom]


||| Compose two computations in the HoareState context. (Largely) isomorphic
||| to the monadic bind (>>=)
hbind : (AssertAtomic s m) => HoareState s m p1 q1 a -> (a -> HoareState s m p2 q2 b) ->
                HoareState s m
                  (p1 :&&: (Df q1) :=>: (Df p2))
                  ((Df q1) :&&: (Df $ Df q2)) b
hbind (HS st) f = HS $
  \p, s =>
    case !(check p s) of
      (True, rp) =>
        let [s', x, rem] =
          !(st rp s) in
        case !(check (rem :&&: rp) s') of
          (True, rp') =>
            case x of
              (Result v) =>
                let HS st' =
                  (f v) in
                let [s'', x', rem'] =
                  !(st' rp' s') in
                case !(check (rem' :&&: rp') s') of
                  (True, rp'') => pure [s'', x', rp'' :&&: rem']
                  (False, _)   => pure [s'', pfail (rem' :&&: rp'), Bottom]
              (Error str) => pure [s', Error str, Bottom]
          (False, rp') =>
            pure [s', pfail (rem :&&: rp), Bottom]
      (False, _) => pure [s, pfail p, Bottom]

||| Get the current state value stored in a HoareState context
hget : (AssertAtomic s m) => HoareState s m Top (Df Top) s
hget = HS $
  \p, s =>
    case !(check p s) of
      (True, rp) => pure [s, Result s, rp]
      (False, _) => pure [s, pfail p, Bottom]


||| Replace the current state value stored in a HoareState context
hput : (AssertAtomic s m) => (x : s) -> HoareState s m Top (Df Top) ()
hput s' = HS $
  \p, s =>
    case !(check p s) of
      (True, rp) => pure [s', Result (), rp]
      (False, _) => pure [s', pfail p, Bottom]

||| Evaluate a computation in the HoareState context to it's resulting
||| value and state
hrun : (Show s, AssertAtomic s m) => {p : Predicate s} -> {q : Predicate s} -> HoareState s m p q a -> s -> m (s, Except a)
hrun {p} {q} (HS st) s =
  case !(check (p :&&: q) s) of
    (True, rp) =>
      let [s', x, rp'] =
        !(st rp s) in
      pure (s', x)
    (False, _) => pure (s, pfail (p :&&: q))

||| Functor implementation for the hoare state
implementation Functor (HoareState s m p q) where
  map f (HS st) = HS $
    \p, s =>
      let [s', x, rp] =
        !(st p s) in
      case x of
        (Result v) => pure [s', Result $ f v, rp]
        (Error e)  => pure [s', Error e, Bottom]

||| Everything below is to overload the do-notation in such a way that it can
||| be used for both the HoareState context as well as any other monad
|||
||| Simply creating an instance of the Monad interface for HoareState is
||| not possible, as the type of hbind does not match that of >>=.
|||
||| A futile attempt to mitigate this issue was made by creating a wrapper
||| that discards the pre- and postcondition. However, with this approach
||| implementing the `pure` function in the required applicative instance
||| proved to be difficult, as there was no easy way to impose the AssertAtomic
||| constraint on the input types `s` and `m`. This is problematic as the
||| constructors needed to implement the `pure` function do impose this
||| contstraint.
|||
||| Obviously, this is a temporary solution/hack, and will
||| (hopefully) be replaced a.s.a.p.temporary

data HWrap : (s : Type) -> (m : Type -> Type) -> (a : Type) -> Type where
  MkHWrap : AssertAtomic s m => HoareState s m p q a -> HWrap s m a

-- Tepm. store of the bind operator
tmpbind : Monad m => m a -> (a -> m b) -> m b
tmpbind = (>>=)

-- Temp. store of the pure function
tmppure : Applicative f => a -> f a
tmppure = pure


-- Hide existing operators
%hide (>>=)
%hide pure

-- Interface overloading the hidden operators, mimicking the `Monad` interface
interface HMonad (m : Type -> Type) where
  pure : a -> m a
  (>>=) : m a -> (a -> m b) -> m b

-- HoareState is an instance of the fake monad as well :)
implementation AssertAtomic s m => HMonad (HWrap s m) where
  pure = MkHWrap . hreturn
  (MkHWrap x) >>= y = MkHWrap (x `hbind` (transf . y))
    where transf : {auto p : Predicate s} -> {auto q : Predicate s} -> HWrap s m b -> HoareState s m p q b
          transf (MkHWrap (HS st))= HS st

-- Annoyingly, idris somehow is convinced that these instances overlap, despite
-- the fact that HWrap is not a member of the `Monad` interface  ... 
%overlapping
implementation Monad m => HMonad m where
  pure = tmppure
  (>>=) = tmpbind
