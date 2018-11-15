module Main

import Environment
import Syntax
import CmdIO

import Data.Vect
import Data.List
import Data.So

import AtomicProofs

||| Describes how errors can be thrown in the context `m`
interface Throwable (m : Type -> Type) where
  throw : String -> m ()

implementation Throwable IO where
  throw = putStrLn

||| Signifies the end of a script
done : a -> CmdF a
done x = liftF (Return)

||| List the contents of the directory contained at the input path
ls : Path -> CmdF (List Path)
ls path = liftF (Ls path id)

||| Output the contents of the file contained at the input path to the command line
cat : Path -> CmdF String
cat path = liftF (Cat path id)

||| Output the input string to the command line
echo : String -> CmdF String
echo str = liftF (Echo str id)

||| Example script using the echo command
echo1 : CmdF ()
echo1 = do
  echo "Foo" >>= echo
  done ()

||| A shorthand for easier notation of permissions
I : Bool
I = True
O : Bool
O = False

||| Get relevant state. This is just a dummy, but since we cannot compile anyways
||| it doesn't really make sense to implement this anyway. 
getState : CmdExec m => m (FSTree, User)
getState = pure ((FSLeaf (MkFileInfo "file1.txt" 
  (MkFileMD F_ [[I,I,I], [I,I,I], [O,O,O]] (U "cas" "user")))), (U "cas" "user"))

||| Run a script, given a function that asserts its precondition (by 
||| giving a proof that it holds, or Nothing)
run : (CmdExec m, Throwable m) =>
      (script : CmdF r) -> ((st : (FSTree, User))
                        -> Maybe (([[..]] (pre script)) st)) -> m ()
run script check = do
  st <- getState
  case check st of
    Nothing => throw "Precondition check failed ..."
    (Just x) => cmdExec script

||| Proves that the precondition of the `echo1` script holds (trivial) 
proveEcho1 : (fs : FSTree) -> Maybe (([[. FSTree .]] (
                                Forall String (\_ =>
                                  Forall String (\_ => T)
                                ))) fs
                              )
proveEcho1 _ = Just $ (const (const ()))

||| Prove that the precondition of the `cat1` script holds (not so trival, but still
||| quite simple)
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

||| A simple script utilizing the cat command
cat1 : CmdF ()
cat1 = do
  cat (FilePath [] "file1.txt")
  done ()
  
catTwice : Path -> CmdF String
catTwice p = do 
  x <- cat p
  y <- cat p
  done (x ++ y)
  
combined : CmdF ()
combined = do 
  ls (DirPath ["example", "path"])
  str <- catTwice (FilePath ["example", "path"] "file1.txt")
  echo str
  done ()
  
asMaybe : Dec a -> Maybe a
asMaybe (Yes x) = Just x
asMaybe _       = Nothing  

syntax "??" [dec] = asMaybe dec
  
proveCombined : (st : (FSTree, User)) -> Maybe (([[. (FSTree, User) .]] 
                    (Atom $ pathExists (DirPath ["example", "path"])) /\
                    (Atom $ hasType (DirPath ["example", "path"]) D_) /\
                    (Atom $ hasAuthority (DirPath ["example", "path"]) R) /\
                    Forall (List Path) (\_ => 
                      (Atom $ pathExists (FilePath ["example", "path"] "file1.txt")) /\ 
                      (Atom $ hasType (FilePath ["example", "path"] "file1.txt") F_) /\
                      (Atom $ hasAuthority (FilePath ["example", "path"] "file1.txt") R) /\
                      Forall String (\_ =>
                        (Atom $ pathExists (FilePath ["example", "path"] "file1.txt")) /\
                        (Atom $ hasType (FilePath ["example", "path"] "file1.txt") F_) /\
                        (Atom $ hasAuthority (FilePath ["example", "path"] "file1.txt") R) /\
                        Forall String (\_ => T)
                      )
                    )
                ) st)
proveCombined (fs, u) = do 
 -- Proofs over the first path
 ext1 <- ?? provePathExists (DirPath ["example", "path"]) fs
 fty1 <- ?? provePathHasType (DirPath ["example", "path"]) D_ ext1
 aut1 <- ?? proveModAllowed (DirPath ["example", "path"]) R u ext1
 
 --Proofs over the second path 
 ext2 <- ?? provePathExists (FilePath ["example", "path"] "file1.txt") fs
 fty2 <- ?? provePathHasType (FilePath ["example", "path"] "file1.txt") F_ ext2
 aut2 <- ?? proveModAllowed (FilePath ["example", "path"] "file1.txt") R u ext2
 
 -- Assemble proofs into final result
 pure (
   ((ext1, (ext1 ** fty1)), (ext1 ** aut1)), 
   const (((ext2, (ext2 ** fty2)), (ext2 ** aut2)), 
     const (
       ((ext2, (ext2 ** fty2)), (ext2 ** aut2)),
     const ())
   )
 )

||| Execute the cat1 script in the IO monad
main : IO ()
main = run combined proveCombined
