module Main

import Environment
import Syntax 
import CmdIO

import Data.Vect
import Data.List
import Data.So

import AtomicProofs

ret : a -> CmdF a 
ret x = liftF (Return)

ls : Path -> CmdF (List Path)
ls path = liftF (Ls path id)

cat : Path -> CmdF String
cat path = liftF (Cat path id)

echo : String -> CmdF String
echo str = liftF (Echo str id)

echo1 : CmdF ()
echo1 = do 
  echo "Foo" >>= echo
  pure ()
 
I : Bool 
I = True 

O : Bool 
O = False

interface Throwable (m : Type -> Type) where 
  throw : String -> m ()
  
implementation Throwable IO where
  throw = putStrLn

||| get file structure  
getFS : CmdExec m => m FSTree  
getFS = pure (FSLeaf (MkFileInfo "file1.txt" (MkFileMD F_ [[I,I,I], [I,I,I], [O,O,O]] (U "cas" "user"))))

run : (CmdExec m, Throwable m) => 
      (script : CmdF r) -> ((fs : FSTree) 
                        -> Maybe ([[..]] (pre script))) -> m () 
run script check = do 
  fs <- getFS
  case check fs of 
    Nothing => throw "Precondition check failed ..."
    (Just x) => cmdExec script

proveEcho1 : (fs : FSTree) -> Maybe ([[. FSTree .]] (
                                Forall String (\_ => 
                                  Forall String (\_ => T)
                                ))
                              )
proveEcho1 _ = Just $ (const (const ()))

total
proveCat1 : (fs : FSTree) -> Maybe ([[. FSTree .]] 
  ((Atom $ pathExists (FilePath [] "file1.txt")) /\ (Forall String (const T))))
proveCat1 fs with (provePathExists fs (FilePath [] "file1.txt"))
  proveCat1 fs | Nothing = Nothing
  proveCat1 fs | (Just x) = Just (x, const ())

cat1 : CmdF ()
cat1 = do
  cat (FilePath [] "file1.txt")
  pure ()

main : IO ()
main = run (cat1) proveCat1
