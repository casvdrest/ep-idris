module Syntax 

-- File system data types
import Environment
import Free

import Data.So
import Control.ST

infixl 5 /\
infixl 4 :=>
infix  6 =:=

infixl 7 <#>

%access public export

data Predicate : Type -> Type where 
  (/\)  : Predicate s -> Predicate s -> Predicate s
  (:=>) : Predicate s -> Predicate s -> Predicate s
  (=:=) : (DecEq a) => a -> a -> Predicate s
  Forall : (a : Type) -> (a -> Predicate s) -> Predicate s
  --Exists : (a : Type) -> (a -> Predicate s) -> Predicate s
  Atom : (s -> Bool) -> Predicate s
  T : Predicate s
  F : Predicate s
  
infix 1 ><

||| Constructs a dependent pair
(><) : (a : Type) -> (a -> Type) -> Type
a >< b = DPair a b

total
tyFromBool : Bool -> Type 
tyFromBool True = Unit
tyFromBool False = Void

total
asType : {s : Type} -> Predicate s -> Type 
asType (p /\ q)  = (asType p, asType q)
asType (p :=> q)  = asType p -> asType q
asType (a =:= b)  = (a = b)
asType (Forall ty p) = ((x : ty) -> asType (p x))
--asType (Exists ty p) = (\s => (ty >< (\x => asType (p x) s)))
asType (Atom f)   = s >< So . f
asType T          = Unit 
asType F          = Void

syntax "[[..]]" [pred] = asType pred
syntax "[[." [ty] ".]]" [pred] = asType {s = ty} pred
  
data Cmd next = Ls Path (List Path -> next) 
              | Cat Path (String -> next)
              | Echo String (String -> next)
              | Return
              
implementation Functor Cmd where 
  map f (Ls x g) = assert_total $ Ls x (\v => f (g v))
  map f (Cat x g) = assert_total $ Cat x (\v => f (g v))
  map f (Echo x g) = assert_total $ Echo x (\v => f (g v))
  map f Return = Return
  
total
any' : (a -> Bool) -> List a -> Bool 
any' p [] = False
any' p (x :: xs) = p x || any' p xs
 
||| Create a predicate that asserts whether the input path is valid in 
||| the filesystem.
total
pathExists : Path -> FSTree -> Bool 
pathExists (FilePath [] y) (FSNode x xs) = False
pathExists (FilePath (z :: ys) y) (FSNode (MkFileInfo name md) xs) = assert_total $
  name == z && any' (pathExists (FilePath ys y)) xs
pathExists (DirPath []) (FSNode x xs) = True
pathExists (DirPath (y :: ys)) (FSNode (MkFileInfo name md) xs) = assert_total $ 
  name == y && any' (pathExists (DirPath ys)) xs
pathExists (FilePath [] y) (FSLeaf (MkFileInfo name md)) = y == name
pathExists (FilePath (z :: xs) y) (FSLeaf x) = False
pathExists (DirPath []) (FSLeaf x) = True
pathExists (DirPath (y :: xs)) (FSLeaf x) = False
  
data CmdF : Type -> Type where
  Bind : Cmd (CmdF a) -> CmdF a
  Pure : a -> CmdF a

||| Functor implementation for the 'Free' datatype
implementation Functor CmdF where
  map f m = assert_total $
    case m of
      (Bind x) => Bind (map (map f) x)
      (Pure x) => Pure (f x)

||| Applicative instance for the 'Free' datatype
implementation Applicative CmdF where
  pure     = Pure
  f <*> g = assert_total $
    case f of
      (Pure m) => map m g
      (Bind m) => Bind (map (<*> g) m)

||| Monad instance for the 'Free' datatype
implementation Monad CmdF where
  f >>= g = assert_total $
    case f of
      (Pure m) => g m
      (Bind m) => Bind (map (>>= g) m)

||| Lift a functor into the free monad
liftF : Cmd a -> CmdF a
liftF m = Bind (map Pure m)

||| Sequential composition of monadic computations
||| (result values are discarded)
(>>) : Monad m => m a -> m b -> m b
f >> g = f >>= const g

total
pre : CmdF a -> Predicate FSTree 
pre (Bind cmd) =
  case cmd of 
    (Ls p cmd) => (Atom $ pathExists p) /\ Forall (List Path) (\lst => pre (cmd lst))
    (Cat p cmd) => (Atom $ pathExists p) /\ Forall String (\str => pre (cmd str))
    (Echo s cmd) => Forall String (\str => pre (cmd str))
    Return => T
pre (Pure _) = T

interface Monad m  => CmdExec (m : Type -> Type) where 
  cmdExec : CmdF a -> m ()
