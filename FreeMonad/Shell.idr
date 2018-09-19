||| Provides a deep embedding for bash shell scripts
module Shell

import Environment
import Free

%access public export

||| Embedding of various shell commands
data Cmd a = Ls
           | Cat
           | Cd
           | Touch

implementation Functor Cmd where
  -- Unfortunately we need to match all the cases, in order to construct
  -- a new term with the correct phantom type.
  map f Ls    = Ls
  map f Cat   = Cat
  map f Cd    = Cd
  map f Touch = Touch

CmdF : Type -> Type
CmdF = Free Cmd

ls : {auto a : Type} -> CmdF a
ls = liftF Ls

cat : {auto a : Type} -> CmdF a
cat = liftF Cat

cd : {auto a : Type} -> CmdF a
cd = liftF Cd

touch : {auto a : Type} -> CmdF a
touch = liftF Touch

script : {auto a : Type} -> CmdF a
script = do
  cd
  ls
  cat
