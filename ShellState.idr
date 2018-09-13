module ShellState 

import Data.HVect

%access export

Name : Type 
Name = String

public export
data User : Type where 
    MkUser : Name -> Name -> User 

public export
Permission : Type
Permission = Vect 3 Bool

public export
FPermission : Type
FPermission = Vect 3 Permission

public export
data FType = F
           | D

public export
data FMod = R
          | W
          | X

public export
data FileMD : Type where
    MkFileMD : FType -> FPermission -> User -> FileMD

public export
data FileInfo : Type where 
    MkFileInfo : String -> FileMD -> FileInfo

public export 
data Path : Type where 
    FilePath : List Name -> Name -> Path 
    DirPath : List Name -> Path

public export
data FSTree : Type where 
    FSLeaf : Name -> FSTree
    FSNode : Name -> List FSTree -> FSTree
     
public export 
data FSInfo : Type where 
    MkFSInfo : List (List FSTree) -> FSInfo

Capability : Type 
Capability = (Path, List FMod)

SState : Type  
SState = HVect [User, FSInfo, List Capability] 

Cmd : String -> Type 
Cmd str = if str == "Int" then Int else Bool

data So : Bool -> Type where 
    Oh : So True

isTen : Int -> Bool 
isTen x = x == 10

f : (x : Int) -> So (isTen x)
f = Oh 
