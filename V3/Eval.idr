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
getFS = pure (FSLeaf (MkFileInfo "file1.txt" 
  (MkFileMD F_ [[I,I,I], [I,I,I], [O,O,O]] (U "cas" "user"))))

run : (CmdExec m, Throwable m) =>
      (script : CmdF r) -> ((fs : FSTree)
                        -> Maybe (([[..]] (pre script)) fs)) -> m ()
run script check = do
  fs <- getFS
  case check fs of
    Nothing => throw "Precondition check failed ..."
    (Just x) => cmdExec script

proveEcho1 : (fs : FSTree) -> Maybe (([[. FSTree .]] (
                                Forall String (\_ =>
                                  Forall String (\_ => T)
                                ))) fs
                              )
proveEcho1 _ = Just $ (const (const ()))

total
proveCat1 : (fs : FSTree) -> Maybe (([[. FSTree .]]
  ((Atom $ pathExists (FilePath [] "file1.txt"))  /\
   (Atom $ hasType (FilePath [] "file1.txt" ) F_) /\
   (Forall String (const T)))) fs)
proveCat1 fs with (provePathExists (FilePath [] "file1.txt") fs)
  proveCat1 fs | (Yes prf1) =
    case provePathHasType (FilePath [] "file1.txt") F_ prf1 of
      (Yes prf2) => Just ((prf1, (prf1 ** prf2)), const ())
      (No contra) => Nothing
  proveCat1 fs | (No contra) = Nothing

cat1 : CmdF ()
cat1 = do
  cat (FilePath [] "file1.txt")
  pure ()

main : IO ()
main = run (echo "Hallo, Wereld!") (\_ => Just (const ()))

is10 : Nat -> Type 
is10 = [[..]] (Atom $ (\n => n = 10))

prove10 : is10 10
prove10 = Refl
