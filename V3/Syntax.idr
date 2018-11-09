module Syntax 

-- File system data types
import Environment
import Free

import Data.So
import Data.Vect
import Data.List
import Control.ST

infixl 5 /\
infixl 4 :=>
infix  6 =:=

%access public export

data Predicate : Type -> Type where 
  (/\)  : Predicate s -> Predicate s -> Predicate s
  (:=>) : Predicate s -> Predicate s -> Predicate s
  (=:=) : (DecEq a) => a -> a -> Predicate s
  Forall : (a : Type) -> (a -> Predicate s) -> Predicate s
  --Exists : (a : Type) -> (a -> Predicate s) -> Predicate s
  Atom : (s -> Type) -> Predicate s
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
asType (Atom f)   = s >< f
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
  
pathExists : (p : Path) -> (fs : FSTree) -> Type
pathExists p fs = FSElem p fs

total
fileFromProof : FSElem p fs -> FileInfo
fileFromProof {fs = (FSNode x xs)} HereDir = x
fileFromProof {fs = (FSLeaf (MkFileInfo n1 md))} 
              (HereFile Refl) = MkFileInfo n1 md
fileFromProof {fs = (FSNode (MkFileInfo n md) ys)} 
              (ThereDir x y z n) = fileFromProof y
fileFromProof {fs = (FSNode (MkFileInfo n md) ys)} 
              (ThereFile y z w n) = fileFromProof z

total
typeIs : FType -> FSElem p fs -> Type
typeIs ft prf = getFType (fileFromProof prf) = ft

total
hasType : (p : Path) -> (t : FType) -> (fs : FSTree) -> Type
hasType p ft fs = FSElem p fs >< typeIs ft
  
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
    (Cat p cmd) => (Atom $ pathExists p) /\ (Atom $ hasType p F_) /\ Forall String (\str => pre (cmd str))
    (Echo s cmd) => Forall String (\str => pre (cmd str))
    Return => T
pre (Pure _) = T

interface Monad m  => CmdExec (m : Type -> Type) where 
  cmdExec : CmdF a -> m ()

