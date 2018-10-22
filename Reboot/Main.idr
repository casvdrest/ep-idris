module Main

import Environment
import Free
import Syntax
import CmdIO

implementation Functor Cmd where
  map f (Ls x g) = assert_total $ Ls x (\v => f (g v))
  map f (Cat x g) = assert_total $ Cat x (\v => f (g v))
  map f (Echo x g) = assert_total $ Echo x (\v => f (g v))
  map f Return = Return

CmdF : Type -> Type
CmdF = Free Cmd

done : Free Cmd ()
done = liftF Return

ls : Path -> Free Cmd (List Path)
ls path = liftF (Ls path id)

cat : Path -> Free Cmd String
cat path = liftF (Cat path id)

echo : String -> Free Cmd String
echo str = liftF (Echo str id)

script : CmdF ()
script = do
  x <- echo "wie is daar"
  echo x >>= echo
  done

main : IO ()
main = implIO script
