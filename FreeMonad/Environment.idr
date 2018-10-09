module Environment

import Data.Vect

%access public export

||| Useful type synonyms
Name : Type
Name = String

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
data FMod = R
          | W
          | X

||| Equality for the various access levels
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

||| Contains all relevant info about files -- e.g. it's name, and metadata
data FileInfo : Type where
  MkFileInfo : (name : Name) -> (md : FileMD) -> FileInfo

||| Models a path through the file system tree
data Path : Type where
  FilePath : List Name -> Name -> Path
  DirPath  : List Name -> Path

||| Define equality for filepaths
implementation Eq Path where
  (FilePath xs x) == (FilePath ys y) = xs == ys && x == y
  (DirPath xs   ) == (DirPath ys)    = xs == ys
  _               == _               = False

infix 6 <?

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

data FSTree = FSNode FileInfo (List FSTree) -- Directories
            | FSLeaf FileInfo               -- Files
