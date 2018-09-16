module TSS.Logic

import public FileSystem

import Control.ST
import Data.Vect
import Data.So

%access public export

||| A Capability is simply a reference to a file, and the action that the script might want
||| to perform on that file
|||
||| Additionally, a boolean flag is passed that indicates whether a capability is recursive,
||| i.e. a recursive capability on a directory means that the same capability is automatically
||| obtained for all files and directories within it.
data Capability : Type where
  MkCapability : Path -> FMod -> Bool -> Capability


||| Define a predicate on a given type as a function from that
||| type to 'Bool'
Pred : Type -> Type
Pred t = t -> Bool

||| The global state (as of yet) consists of three main components:
||| * The current user
||| * A list of capabilities used by the script
||| * File system information
|||
||| Note that the number of capabilities and relevant file system fragments
||| is required to be equal.
data ShellState : Type where
  MkShellState : User -> FSTree
                      -> List Capability
                      -> ShellState

data Command : Type where
   MkCommand : (Pred ShellState) -> (ShellState -> ShellState)
                                 -> (Pred ShellState)
                                 -> Command

||| Info about user defined commands
data BinaryInfo : Type where
  MkBinaryInfo : String -> Command -> BinaryInfo

-- Define special notation for defining pre and post conditions
syntax "{{" [pre] "}}-" [f] "-{{" [post] "}}" = MkCommand pre f post
syntax assume [name] as [command] = MkBinaryInfo name command

infixl 7 ===>
infixl 6 /\
infixl 5 \/
infixl 4 <==>

-- Boolean negation; this is a unary operator so use a special syntax
-- definition
syntax "~" [pred] = not . pred

||| Atomic 'True'
true : a -> Bool
true = const True

||| Atomic 'False'
false : a -> Bool
false = ~true

||| Conjunction
(/\) : (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p /\ q = (\v => p v && q v)

||| Disjunction
(\/) : (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p \/ q = (\v => p v || q v)

||| Implication
(===>) : (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p ===> q = ~p /\ q

||| Bi-Implication
(<==>) : (a -> Bool) -> (a -> Bool) -> (a -> Bool)
(<==>) p q = p ===> q /\ q ===> p

||| Assert that a file exists in the state represented by the tree
||| contained in the current state
exists : Path -> ShellState -> Bool
exists path (MkShellState _ fs _) = isJust (getFile path fs)

||| Asserts whether the vertex contained at the provided path is a file in
||| the file tree contained in the shell state
isFile : Path -> ShellState -> Bool
isFile path (MkShellState _ fs _) =
  case getFile path fs of
    (Just (MkFileInfo _ (MkFileMD t _ _))) => t == F
    Nothing                                => False

||| Asserts whether the vertex contained at the provided path is a directory in
||| the file tree contained in the shell state
isDirectory : Path -> ShellState -> Bool
isDirectory path st = not (isFile path st)

||| Assert that the current user has read access to the file contained at
||| The given path
accessRead : Path -> ShellState -> Bool
accessRead path (MkShellState u fs _) =
  case getFile path fs of
    (Just (MkFileInfo _ md)) => canRead u md
    Nothing                  => False
