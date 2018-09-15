module TSS.Logic

import public FileSystem

import Control.ST
import Data.Vect

%access public export

||| A Capability is simply a reference to a file, and the action that the script might want
||| to perform on that file
|||
||| Additionally, a boolean flag is passed that indicates whether a capability is recursive,
||| i.e. a recursive capability on a directory means that the same capability is automatically
||| obtained for all files and directories within it.
data Capability : Type where
  MkCapability : Path -> FMod -> Bool -> Capability

||| The global state (as of yet) consists of three main components:
||| * The current user
||| * A list of capabilities used by the script
||| * A list of file system fragments, resulting from capabilities
|||
||| Note that the number of capabilities and relevant file system fragments
||| is required to be equal.
ShellState : {n : Nat} -> Type
ShellState {n} =
  Composite
    [ State User
    , State (Vect n Capability)
    , State (Vect n FSTree    )
    ]

||| Define a predicate on a given type as a function from that
||| type to 'Bool'
Pred : Type -> Type
Pred t = t -> Bool

data Command : Type where
   MkCommand : (Pred ShellState) -> (ShellState -> ShellState)
                                 -> (Pred ShellState)
                                 -> Command

||| Info about user defined commands
data BinaryInfo : Type where
  MkBinaryInfo : String -> Command -> BinaryInfo

-- Syntax definitions to make the definition of commands easier
syntax "{{" [pre] "}}-" [f] "-{{" [post] "}}" = MkCommand pre f post
syntax assume [name] as [command] = MkBinaryInfo name command
syntax "~" [pred] = not . pred

infixl 6 /\
infixl 5 \/

(/\) : (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p /\ q = (\v => p v && q v)

(\/) : (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p \/ q = (\v => p v || q v)

exists : Path -> ShellState -> Bool
exists = ?exists

isFile : Path -> ShellState -> Bool
isFile = ?isFile

isDirectory : Path -> ShellState -> Bool
isDirectory = ?isDirectory

accessRead : Path -> ShellState -> Bool
accessRead = ?accessRead
