||| Contains an implementation for the free monad
module Free

%access public export

using (f : (Type -> Type), a : Type)
  ||| Free data type: Free f a = Pure a | Bind (f (Free f a))
  data Free : (Type -> Type) -> a -> Type where
    Bind : f (Free f a) -> Free f a
    Pure : a -> Free f a

||| Functor implementation for the 'Free' datatype
implementation Functor f => Functor (Free f) where
  map f m = assert_total $
    case m of
      (Bind x) => Bind (map (map f) x)
      (Pure x) => Pure (f x)

||| Applicative instance for the 'Free' datatype
implementation Functor f => Applicative (Free f) where
  pure     = Pure
  f <*> g = assert_total $
    case f of
      (Pure m) => map m g
      (Bind m) => Bind (map (<*> g) m)

||| Monad instance for the 'Free' datatype
implementation Functor f => Monad (Free f) where
  f >>= g = assert_total $
    case f of
      (Pure m) => g m
      (Bind m) => Bind (map (>>= g) m)

||| Lift a functor into the free monad
liftF : Functor f => f a -> Free f a
liftF m = Bind (map Pure m)

||| Sequential composition of monadic computations
||| (result values are discarded)
(>>) : Monad m => m a -> m b -> m b
f >> g = f >>= const g
