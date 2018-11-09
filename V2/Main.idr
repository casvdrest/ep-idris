module Main

import HoareState
import HoareExample

main : IO ()
main = do
  (s, a) <- hrun iget 10
  print a
  pure ()
