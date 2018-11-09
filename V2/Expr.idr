module Main

import Data.Vect
import Control.Monad.State
import Free

%access public export

infixr 6 :+:
infixr 5 :<:

data (:+:) : (f : Type -> Type) -> (g : Type -> Type) -> Type -> Type where
  Inl : f e -> (f :+: g) e
  Inr : g e -> (f :+: g) e

implementation (Functor f, Functor g) => Functor (f :+: g) where
  map f (Inl x) = Inl (map f x)
  map f (Inr x) = Inr (map f x)

data (:<:) : (Type -> Type) -> (Type -> Type) -> Type where
	Ref : (Functor f) => f :<: f
	Co : (Functor f, Functor g) => f :<: (f :+: g)
	Ind : (Functor f, Functor g, Functor h) => {auto prf : f :<: g} -> f :<: h :+: g

inj : {p : f :<: g} -> f a -> g a
inj {p} x with (p)
	inj x | Ref       = x
	inj x | Co        = Inl x
	inj x | Ind {prf} = Inr (inj {p = prf} x)

inject : (Functor f, Functor g) => {auto prf : g :<: f} -> g (Free f a) -> Free f a
inject {prf} = Bind . (inj {p = prf})

foldTerm : Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
foldTerm pure imp (Pure x) = pure x
foldTerm pure imp (Bind t) = imp (map (foldTerm pure imp) t)

data Mem = M Int

interface (Functor f, Monad m) => Run (f : Type -> Type) (m : Type -> Type) where
  runAlgebra : f (m a) -> m a

data Recall : Type -> Type where
  MkRecall : (Int -> t) -> Recall t

data Incr : Type -> Type where
  MkIncr : Int -> t -> Incr t

implementation Functor Recall where
  map f (MkRecall t) = MkRecall (\i => f (t i))

implementation Functor Incr where
  map f (MkIncr t x) = MkIncr t (f x)

implementation MonadState Int m => Run Incr m where
  runAlgebra (MkIncr m r) = put m >> r

implementation MonadState Int m => Run Recall m where
  runAlgebra (MkRecall r) = r (!get)

implementation (Run f m, Run g m) => Run (f :+: g) m where
  runAlgebra (Inl r) = runAlgebra r
  runAlgebra (Inr r) = runAlgebra r
