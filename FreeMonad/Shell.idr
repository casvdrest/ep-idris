||| Provides a deep embedding for bash shell scripts
module Shell

import Environment
import Free

import Data.HVect
import Data.Fin

import Debug.Error as Debug.Error

%access public export

%language ElabReflection

||| Embedding of various shell commands
data Cmd next = Ls    next
              | Cat   next
              | Cd    next
              | Touch next
              | Stop

implementation Functor Cmd where
  map f (Ls    x) = Ls     (f x)
  map f (Cat   x) = Cat    (f x)
  map f (Cd    x) = Cd     (f x)
  map f (Touch x) = Touch  (f x)
  map f  Stop     = Stop

CmdDesc : (Type -> Type) -> Type -> Type
CmdDesc m a = HVect [m a, m a, m a, m a, m a]

data CmdAlgebra : (Type -> Type ) -> Type -> Type where
  MkCmdAlgebra : (Monad m) => CmdDesc m a -> CmdAlgebra m a

uwrap : (Monad m) => CmdAlgebra m a -> CmdDesc m a
uwrap (MkCmdAlgebra hvect) = hvect

CmdF : next -> Type
CmdF = Free Cmd

UnitF : (Type -> Type) -> Type
UnitF m = Free m Unit

ls : {auto a : Type} -> CmdF (UnitF m)
ls = liftF (Ls (Pure ()))

cat : CmdF (UnitF m)
cat = liftF (Cat (Pure ()))

cd : CmdF (UnitF m)
cd = liftF (Cd (Pure ()))

touch : CmdF (UnitF m)
touch = liftF (Touch (Pure ()))

stop : CmdF (UnitF m)
stop = liftF Stop

interface Error (f : Type -> Type) where
  throw : f a

implementation Error IO where
  throw = Debug.Error.error "AN ERROR BRO"

interpret : (Monad m, Error m) => CmdAlgebra m a -> CmdF next -> m a
interpret alg (Bind (Ls next))    =
  index FZ (uwrap alg)                >> interpret alg next
interpret alg (Bind (Cat next))   =
  index (FS FZ) (uwrap alg)           >> interpret alg next
interpret alg (Bind (Cd next))    =
  index (FS (FS FZ)) (uwrap alg)      >> interpret alg next
interpret alg (Bind (Touch next)) =
  index (FS (FS (FS FZ))) (uwrap alg) >> interpret alg next
interpret alg (Bind Stop)         =
  index (FS (FS (FS (FS FZ)))) (uwrap alg)
interpret alg (Pure _) = ?rhs

CmdIO : CmdAlgebra IO ()
CmdIO = MkCmdAlgebra [putStr "ls\n", putStr "cat\n", putStr "cd\n", putStr "touch\n", putStr "stop\n"]

exec : CmdF next -> IO ()
exec = interpret CmdIO

script : {next : Type} -> CmdF next
script = ls
