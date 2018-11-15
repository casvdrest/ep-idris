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
getState : CmdExec m => m (FSTree, User)
getState = pure ((FSLeaf (MkFileInfo "file1.txt" 
  (MkFileMD F_ [[I,I,I], [I,I,I], [O,O,O]] (U "cas" "user")))), (U "cas" "user"))

run : (CmdExec m, Throwable m) =>
      (script : CmdF r) -> ((st : (FSTree, User))
                        -> Maybe (([[..]] (pre script)) st)) -> m ()
run script check = do
  st <- getState
  case check st of
    Nothing => throw "Precondition check failed ..."
    (Just x) => cmdExec script

proveEcho1 : (fs : FSTree) -> Maybe (([[. FSTree .]] (
                                Forall String (\_ =>
                                  Forall String (\_ => T)
                                ))) fs
                              )
proveEcho1 _ = Just $ (const (const ()))

total
proveCat1 : (st : (FSTree, User)) -> Maybe (([[. (FSTree, User) .]]
  ((Atom $ pathExists (FilePath [] "file1.txt"))  /\
   (Atom $ hasType (FilePath [] "file1.txt" ) F_) /\
   (Atom $ hasAuthority (FilePath [] "file1.txt") R) /\
   (Forall String (const T)))) st)
proveCat1 (fs, u) with (provePathExists (FilePath [] "file1.txt") fs)
  proveCat1 (fs, u) | (Yes prf1) =
    case provePathHasType (FilePath [] "file1.txt") F_ prf1 of
      (Yes prf2) => 
        case proveModAllowed (FilePath [] "file1.txt") R u prf1 of 
          (Yes prf3) => Just (((prf1, (prf1 ** prf2)), (prf1 ** prf3)), const ())
          (No contra) => Nothing
      (No contra) => Nothing
  proveCat1 (fs, u) | (No contra) = Nothing

cat1 : CmdF ()
cat1 = do
  cat (FilePath [] "file1.txt")
  pure ()

main : IO ()
main = run cat1 proveCat1
