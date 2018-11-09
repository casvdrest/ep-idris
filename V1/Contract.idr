module TSS.Logic

import public FileSystem

import Control.ST
import Data.Vect
import Data.So

%access public export

||| A Capability is simply a reference to a file, and the action that the script might want
||| to perform on that file
data Capability : Path -> FMod -> Type where
  MkCapability : (path : Path) -> (mod : FMod) -> Capability path mod

Require : Capability path mod -> Type
Require x = Require x

||| The global state (as of yet) consists of three main components:
||| * The current user
||| * A list of capabilities used by the script
||| * File system information
|||
||| Note that the number of capabilities and relevant file system fragments
||| is required to be equal.
data SSt : Type where
  MkSSt : User -> FSTree -> SSt


||| Define a Pred on a given type as a function from that
||| type to 'Bool'
data Pred : List Type -> Type where
  MkPred : (SSt -> Bool) -> (cpbs : List Type) -> Pred cpbs

data CmdInfo : Pred xs -> (SSt -> SSt) -> Pred ys -> Type where
  MkCmdInfo : (pre : Pred x) -> (f : SSt -> SSt)
                           -> (post : Pred y)
                           -> CmdInfo pre f post

-- Define special notation for defining pre and post conditions
syntax "{{" [pre] "}}-" [f] "-{{" [post] "}}" = MkCmdInfo pre f post
syntax assume [name] as [command] = MkBinaryInfo name command

infix 2 ~>

(~>) : {pre : Pred xs} -> CmdInfo pre f post
                       -> ({contract : Var} -> ST IO () [contract ::: Composite xs])
                       -> {contract : Var} -> ST IO () [contract ::: Composite xs]
_ ~> exec = exec

||| Info about user defined commands
data BinaryInfo : Pred x -> (SSt -> SSt) -> Pred y -> Type where
  MkBinaryInfo : String -> CmdInfo pre f post -> BinaryInfo pre f post

infixl 7 ===>
infixl 6 /\
infixl 5 \/
infixl 4 <==>

negate : Pred xs -> Pred xs
negate (MkPred f xs) = MkPred (not . f) xs

-- Boolean negation; this is a unary operator so use a special syntax
-- definition
syntax "~" [pred] = negate pred

||| Atomic 'True'
true : Pred []
true = MkPred (const True) []

||| Atomic 'False'
false : Pred []
false = ~true

||| Conjunction
(/\) : Pred xs -> Pred ys -> Pred (xs ++ ys)
(MkPred p xs) /\ (MkPred q ys) =
  MkPred (\st =>
    p st && q st
  ) (xs ++ ys)

||| Disjunction
(\/) : Pred xs -> Pred ys -> Pred (xs ++ ys)
(MkPred p xs) \/ (MkPred q ys) =
  MkPred (\st =>
    p st || q st
  ) (xs ++ ys)

||| Implication
(===>) : Pred xs -> Pred ys -> Pred (xs ++ ys)
p ===> q = ~p /\ q

||| Assert that a file exists in the state represented by the tree
||| contained in the current state
exists : Path -> Pred []
exists path =
  MkPred
    (\(MkSSt _ fs) =>
      isJust (getFile path fs)
    ) []

||| Asserts whether the vertex contained at the provided path is a file in
||| the file tree contained in the shell state
isFile : Path -> Pred []
isFile path =
  MkPred
    (\(MkSSt _ fs) =>
      case getFile path fs of
        (Just (MkFileInfo _ (MkFileMD t _ _))) => t == F
        Nothing                                => False
    ) []

||| Asserts whether the vertex contained at the provided path is a directory in
||| the file tree contained in the shell state
isDirectory : Path -> Pred []
isDirectory path = ~(isFile path)

||| Assert that the current user has read access to the file contained at
||| The given path
accessRead : (path : Path) -> Pred [Require (MkCapability path R)]
accessRead path =
  MkPred
    (\(MkSSt u fs) =>
      case getFile path fs of
        (Just (MkFileInfo _ md)) => canRead u md
        Nothing                  => False
    ) [Require (MkCapability path R)]
