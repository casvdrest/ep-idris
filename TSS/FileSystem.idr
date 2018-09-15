module TSS.FileSystem

import Data.HVect
import Data.So
import Control.ST

%access public export

||| Useful type synonym.
Name : Type
Name = String

||| A group is simply defined by its name
Group : Type
Group = Name

||| A linux user
data User : Type where
  U : Name -> Group -> User

||| A single permission entry. Contains 3 bits, respectively indicating
||| read, write and execute (rwx) permission.
Permission : Type
Permission = Vect 3 Bool

||| A file's permission consists of three groups of permissions:
||| * The owner's permissions on the file
||| * The owner's group's permissions on the file
||| * Permissions of all others
FPermission : Type
FPermission = Vect 3 Permission

||| Different types of files that may live in a Linux file system. Currently,
||| symlinks are not included
data FType = F
           | D

||| Define equality for file types
Eq FType where
    F == F = True
    D == D = True
    _ == _ = False

||| Describes three possible operations on files. Depending on wether
||| the object file is an actual file, or a directory, the semantics
||| of each operation may vary.
|||
||| For example, in case of directories, reading is equivalent to obtaining
||| a directory listing, and writing is equivalent to adding/removing/relocating
||| withing/from/to the directory. The execute bit allows users to enter the
||| enter the directory, and access files/directories inside.
data FMod = R
          | W
          | X

||| File metadata. The following information is included:
||| * Type of the file
||| * Permission bits
||| * Owner (user object)
data FileMD : FType -> FPermission -> User -> Type where
  MkFileMD : (t : FType) -> (p : FPermission) -> (u : User) -> FileMD t p u

||| Contains all relevant info about files -- e.g. it's name, and metadata
data FileInfo : Name -> FileMD t p u -> Type where
  MkFileInfo : (name : Name) -> (md : FileMD t p u) -> FileInfo name md

||| Models a path through the file system tree
data Path : Type where
  MkPath : List Name -> Maybe Name -> Path

||| Asserts that the provided file metadata belongs to a directory
isFile : FileMD F p u -> Bool
isFile _ = True

||| Asserts that the provided file metadata belongs to a file
isDir : FileMD D p u -> Bool
isDir _ = True

||| Models (part) of a file system tree. In essence, this is simply a Rose tree,
||| where the nodes represent directories and leaves files.
|||
||| There is one key difference however: leaves are not represented as nodes with an empty
||| list of children, but rather as a separate data constructor. This is necessary
||| to avoid ambiguity, since directories (nodes) may have an empty list of children
||| if they don't contain any files.
|||
||| Clearly, a (partial) path to a file (or directory) can be obtained by gathering
||| the names from all parent nodes starting from the corresponding node/leaf.
|||
||| To prevent the construction of semantically incorrect values for this type,
||| a proof stating that the provided file is of the correct type is required.
data FSTree : Type where
  FSLeaf : ( info : FileInfo name md ) -> {auto p : So (isFile md) } -> FSTree
  FSNode : ( info : FileInfo name md ) -> {auto p : So (isDir  md) } -> List (FSTree) -> FSTree
