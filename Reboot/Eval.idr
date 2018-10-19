module Eval 

import Environment
import Free
import Syntax 
import CmdIO

implementation Functor Cmd where 
  map f (Ls x g) = assert_total $ Ls x (f g)
  map f (Cat x g) = assert_total $ Cat x (f g)
  map f (Echo x g) = assert_total $ Echo x (f g)
  map f (Return x) = Return (f x)
  
CmdF : Type -> Type
CmdF = Free Cmd

ret : a -> Free Cmd a 
ret x = liftF (Return x)

stop : a -> Cmd ()
stop = const $ Return ()

ls : Path -> Free Cmd ()
ls path = liftF (Ls path stop)

cat : Path -> Free Cmd ()
cat path = liftF (Cat path stop)

echo : String -> Free Cmd () 
echo str = liftF (Echo str stop)

script : CmdF ()
script = do 
  echo "hallo"
  echo "wie is daar" 
 
eval : (Show a) => CmdF a -> IO ()
eval (Bind (Ls x c)) = do
  r <- implIO (Ls x c)
  eval r
  
 
 
