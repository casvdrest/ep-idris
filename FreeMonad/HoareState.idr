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

||| Interface for monads that are able to assert atomic predicates
||| Typically, the IO monad is used for this, but by making the
||| computation context parameterizable, another context can be used
||| for testing purposes
interface Monad m => AssertAtomic (s : Type) (m : Type -> Type) where
  total assertAtom : Atom s -> s -> m Bool

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
  At : Atom s -> Predicate s

  -- The 'Df' (Defer) constructor indicates that the contained predicate
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


implementation Show a => Show (Except a) where
  show (Result x) = show x
  show (Error msg) = "(Error " <> msg <> ")"

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

--- HoareState (s : Type) (P : Predicate s) (Q : Predicate (a,s))
---     HS : (i : s) -> P i -> Sigma (a,s) Q

--- exec : (hs : HoareState s a) -> IO (Sigma a (post hs))
--- exec hs = do
--     fs <- getFileSystem 
--     case checkPre hs fs
--       ok prf -> hs (fs,prf)
--       _ -> error "precondition fails"

{-
>>= : HS s a -> (a -> HS s b) -> HS s b
>>= c f s = 
  let (x,s') = c s in
  f x s'
-}
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

implementation Functor Except where
  map f (Result x) = Result (f x)
  map f (Error e ) = Error e

implementation Applicative Except where
  pure = Result

  (Result f) <*> (Result x) = Result (f x)
  (Error e)  <*> _          = Error e
  _          <*> (Error e)  = Error e

||| Functor implementation for the hoare state
implementation Functor (HoareState s m p q) where
  map f (HS st) = HS $
    \p, s =>
      let [s', x, rp] =
        !(st p s) in
      case x of
        (Result v) => pure [s', Result $ f v, rp]
        (Error e)  => pure [s', Error e, Bottom]

||| Applicative implementation for the hoare state
implementation AssertAtomic s m => Applicative (HoareState s m p q) where
  pure a = HS $
    \p, s => pure [s, Result a, p]
  (HS st) <*> (HS st') = HS $
    \p, s =>
      let [s', f, rp] =
        !(st p s) in
      let [s'', y, rp'] =
        !(st' p s) in
       pure [s'', (f <*> y), rp']

increment : AssertAtomic Int m => {s : Int} -> HoareState Int m (At (StateEq s)) (Df (At (StateEq (s + 1)))) ()
increment = HS $
  \p, s => pure [s + 1, Result (), p]
