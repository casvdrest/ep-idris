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
implementation Eq FType where
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

implementation Eq FMod where
  R == R = True
  W == W = True
  X == X = True
  _ == _ = False

||| File metadata. The following information is included:
||| * Type of the file
||| * Permission bits
||| * Owner (user object)
data FileMD : Type where
  MkFileMD : (t : FType) -> (p : FPermission) -> (u : User) -> FileMD

typeFromMD : FileMD -> FType
typeFromMD (MkFileMD t _ _) = t

||| Contains all relevant info about files -- e.g. it's name, and metadata
data FileInfo : Type where
  MkFileInfo : (name : Name) -> (md : FileMD) -> FileInfo

||| Models a path through the file system tree
data Path : Type where
  FilePath : List Name -> Name -> Path
  DirPath  : List Name -> Path

implementation Eq Path where
  (FilePath xs x) == (FilePath ys y) = xs == ys && x == y
  (DirPath xs   ) == (DirPath ys)    = xs == ys
  _               == _               = False

||| Models (part) of a file system tree. In essence, this is simply a Rose tree,
||| where the nodes represent directories and leaves files.
|||
||| There is one key difference however: leaves are not represented as nodes with an empty
||| list of children, but rather as a separate data constructor. This is necessary
||| to avoid ambiguity, since directori
||| if they don't contain any files.
|||
||| Clearly, a (partial) path to a file (or directory) can be obtained by gathering
||| the names from all parent nodes starting from the corresponding node/leaf.
data FSTree : Type where
  FSLeaf : ( info : FileInfo) -> FSTree
  FSNode : ( info : FileInfo) -> List FSTree -> FSTree

||| Retrieve the file situated at the given path from a file system tree
getFile : Path -> FSTree -> Maybe FileInfo
getFile (FilePath [] name) (FSLeaf finfo) =
  case finfo of
    (MkFileInfo n _) => if n == name then Just finfo else Nothing
getFile (FilePath [] _) (FSNode _ _) = Nothing
getFile (FilePath (x :: xs) name) (FSNode (MkFileInfo n _) tree) =
  if n == x then
   listToMaybe $ mapMaybe (getFile (FilePath xs name)) tree
  else Nothing
getFile (FilePath (x :: xs) _) (FSLeaf _) = Nothing

infix 10 <?

||| Extract a single permission bit
(<?) : Permission -> FMod -> Bool
[rp,_,_] <? R = rp
[_,wp,_] <? W = wp
[_,_,xp] <? X = xp

||| Get the owner's permissions for a file
pOwner : FPermission -> Permission
pOwner [ow,_,_] = ow

||| Get the owner's group's permissions for a file
pGroup : FPermission -> Permission
pGroup [_,gr,_] = gr

||| Get other's permissions for a file
pOther : FPermission -> Permission
pOther [_,_,ot] = ot

||| Assert that a given user is allowed to perform a certain modification on
||| a file
modAllowed : FMod -> User -> FileMD -> Bool
modAllowed mod (U uname ugroup) (MkFileMD _ fperm (U fowner fgroup)) =
  (uname == fowner  && ((pOwner fperm) <? mod)) ||
  (ugroup == fgroup && ((pGroup fperm) <? mod)) ||
  ((pOther fperm) <? mod)

||| Assert that a user is allowed to read a file
canRead : User -> FileMD -> Bool
canRead = modAllowed R

||| Assert that a user is allowed to write to a file
canWrite : User -> FileMD -> Bool
canWrite = modAllowed W

||| Assert that a user is allowed to execute a file
canExecute : User -> FileMD -> Bool
canExecute = modAllowed X
