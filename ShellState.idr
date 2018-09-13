module ShellState 

import Data.HVect

%access public export

Name : Type 
Name = String

data User : Type where 
    MkUser : Name -> Name -> User 

Permission : Type
Permission = Vect 3 Bool

FPermission : Type
FPermission = Vect 3 Permission

data FType = F
           | D

Eq FType where 
    F == F = True 
    D == D = True 
    _ == _ = False

data FMod = R
          | W
          | X

data FileMD : Type where
    MkFileMD : FType -> FPermission -> User -> FileMD

ftype : FileMD -> FType 
ftype (MkFileMD type _ _) = type

data FileInfo : FType -> Type where 
    MkFileInfo : String -> (md : FileMD) -> FileInfo (ftype md)

data Path : Type where 
    FilePath : List Name -> Name -> Path 
    DirPath : List Name -> Path

data FSTree : Type where 
    FSLeaf : Name -> FileInfo F -> FSTree
    FSNode : Name -> FileInfo D -> List FSTree -> FSTree
     
data FSInfo : Type where 
    MkFSInfo : List (List FSTree) -> FSInfo

Capability : Type 
Capability = (Path, List FMod)

SState : Type  
SState = HVect [User, FSInfo, List Capability] 