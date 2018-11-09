module Main

import Environment
import Free
import Syntax
import CmdIO

done : CmdF ()
done = liftF Return

ls : Path -> CmdF (List Path)
ls path = liftF (Ls path id)

cat : Path -> CmdF String
cat path = liftF (Cat path id)

echo : String -> CmdF String
echo str = liftF (Echo str id)

script : CmdF ()
script = do
  x <- echo "wie is daar"
  echo x >>= echo
  done

main : IO ()
main = implIO script
