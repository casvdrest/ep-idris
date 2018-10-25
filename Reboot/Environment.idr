module Environment

import Data.Vect
import Data.List

%access public export

||| Useful type synonyms
Name : Type
Name = String

Group : Type
Group = Name

||| A linux user
data User : Type where
  U : Name -> Group -> User
  
implementation Eq User where
  (U x y) == (U z w) = z == x && y == w
  
userEq : x = y -> z = w -> U x z = U y w
userEq Refl Refl = Refl

uEqFromUser : U x z = U y w -> x = y
uEqFromUser Refl = Refl

gEqFromUser : U x z = U y w -> z = w
gEqFromUser Refl = Refl

userNeqName : (x = y -> Void) -> U x z = U y w -> Void
userNeqName contra prf = contra (uEqFromUser prf)

userNeqGroup : (z = w -> Void) -> U x z = U y w -> Void
userNeqGroup contra prf = contra (gEqFromUser prf)
  
implementation DecEq User where 
  decEq (U x y) (U z w) = 
    case decEq x z of
      (Yes prf1) => 
        case decEq y w of 
          (Yes prf2) => Yes $ userEq prf1 prf2
          (No contra) => No $ userNeqGroup contra
      (No contra) => No $ userNeqName contra

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
data FType = F_
           | D_

||| Define equality for file types
implementation Eq FType where
  F_ == F_ = True
  D_ == D_ = True
  _ == _ = False
  
fNotd : F_ = D_ -> Void
fNotd Refl impossible
  
implementation DecEq FType where 
  decEq F_ F_ = Yes Refl
  decEq F_ D_ = No fNotd
  decEq D_ F_ = No (negEqSym fNotd)
  decEq D_ D_ = Yes Refl

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
  
wNotx : W = X -> Void
wNotx Refl impossible

xNotr : X = R -> Void
xNotr Refl impossible

rNotw : R = W -> Void
rNotw Refl impossible
  
implementation DecEq FMod where 
  decEq R R = Yes Refl
  decEq R W = No rNotw
  decEq R X = No (negEqSym xNotr)
  decEq W R = No (negEqSym rNotw)
  decEq W W = Yes Refl
  decEq W X = No (wNotx)
  decEq X R = No (xNotr)
  decEq X W = No (negEqSym wNotx)
  decEq X X = Yes Refl

||| File metadata. The following information is included:
||| * Type of the file
||| * Permission bits
||| * Owner (user object)
data FileMD : Type where
  MkFileMD : (t : FType) -> (p : FPermission) -> (u : User) -> FileMD
  
implementation Eq FileMD where 
  (MkFileMD t p u) == (MkFileMD x xs y) = t == x && p == xs && u == y
  
tyEqFromMD : MkFileMD t p u = MkFileMD x xs y -> t = x
tyEqFromMD Refl = Refl

pmEqFromMD : MkFileMD t p u = MkFileMD x xs y -> p = xs
pmEqFromMD Refl = Refl

uEqFromMD : MkFileMD t p u = MkFileMD x xs y -> u = y
uEqFromMD Refl = Refl

tyNotEqual : (t = x -> Void) -> MkFileMD t p u = MkFileMD x xs y -> Void
tyNotEqual contra = contra . tyEqFromMD

pmNotEqual : (p = xs -> Void) -> MkFileMD t p u = MkFileMD x xs y -> Void
pmNotEqual contra = contra . pmEqFromMD

uNotEqual : (u = y -> Void) -> MkFileMD t p u = MkFileMD x xs y -> Void
uNotEqual contra = contra . uEqFromMD

mdEq : t = x -> p = xs -> u = y -> MkFileMD t p u = MkFileMD x xs y
mdEq Refl Refl Refl = Refl
  
implementation DecEq FileMD where 
  decEq (MkFileMD t p u) (MkFileMD x xs y) = 
    case decEq t x of
      (Yes prf1) => 
        case decEq p xs of 
          (Yes prf2) => 
            case decEq u y of 
              (Yes prf3) => Yes (mdEq prf1 prf2 prf3)
              (No contra) => No (uNotEqual contra)
          (No contra) => No (pmNotEqual contra)
      (No contra) => No (tyNotEqual contra)

||| Contains all relevant info about files, e.g. it's name, and metadata
data FileInfo : Type where
  MkFileInfo : (name : Name) -> (md : FileMD) -> FileInfo
  
implementation Eq FileInfo where 
  (MkFileInfo name md) == (MkFileInfo x y) = name == x && md == y
  
nameEqFromFiEq : MkFileInfo n1 md1 = MkFileInfo n2 md2 -> n1 = n2
nameEqFromFiEq Refl = Refl
  
nameNotEqual : (n1 = n2 -> Void) -> MkFileInfo n1 md1 = MkFileInfo n2 md2 -> Void
nameNotEqual contra = contra . nameEqFromFiEq

mdEqFromFiEq : MkFileInfo n1 md1 = MkFileInfo n2 md2 -> md1 = md2
mdEqFromFiEq Refl = Refl

mdNotEqual : (md1 = md2 -> Void) -> MkFileInfo n1 md1 = MkFileInfo n2 md2 -> Void 
mdNotEqual contra = contra . mdEqFromFiEq

fiEq : n1 = n2 -> md1 = md2 -> MkFileInfo n1 md1 = MkFileInfo n2 md2
fiEq Refl Refl = Refl
  
implementation DecEq FileInfo where 
  decEq (MkFileInfo n1 md1) (MkFileInfo n2 md2) = 
    case decEq n1 n2 of 
      (Yes prf1) => 
        case decEq md1 md2 of 
          (Yes prf2) => Yes (fiEq prf1 prf2)
          (No contra) => No (mdNotEqual contra)
      (No contra) => No (nameNotEqual contra)

||| Models a path through the file system tree
data Path : Type where
  FilePath : List Name -> Name -> Path
  DirPath  : List Name -> Path

||| Define equality for filepaths
implementation Eq Path where
  (FilePath xs x) == (FilePath ys y) = xs == ys && x == y
  (DirPath xs   ) == (DirPath ys)    = xs == ys
  _               == _               = False
  
fileNotDir : FilePath xs x = DirPath ys -> Void 
fileNotDir Refl impossible
  
dpEqFromCmps : xs = ys -> DirPath xs = DirPath ys 
dpEqFromCmps Refl = Refl

cmpsEqFromDp : DirPath xs = DirPath ys -> xs = ys
cmpsEqFromDp Refl = Refl

cmpsNotEqualDp : (xs = ys -> Void) -> DirPath xs = DirPath ys -> Void
cmpsNotEqualDp contra = contra . cmpsEqFromDp

fpEq : xs = ys -> x = y -> FilePath xs x = FilePath ys y
fpEq Refl Refl = Refl

cmpsEqFromFp : FilePath xs x = FilePath ys y -> xs = ys
cmpsEqFromFp Refl = Refl

nameEqFromFp : FilePath xs x = FilePath ys y -> x = y
nameEqFromFp Refl = Refl

cmpsNotEqualFp : (xs = ys -> Void) -> FilePath xs x = FilePath ys y -> Void 
cmpsNotEqualFp contra = contra . cmpsEqFromFp

nameNotEqualFp : (x = y -> Void) -> FilePath xs x = FilePath ys y -> Void 
nameNotEqualFp contra = contra . nameEqFromFp
 
implementation DecEq Path where 
  decEq (FilePath xs x) (FilePath ys y) = 
    case decEq xs ys of 
      (Yes prf1) => 
        case decEq x y of 
          (Yes prf2) => Yes (fpEq prf1 prf2)
          (No contra) => No (nameNotEqualFp contra)
      (No contra) => No (cmpsNotEqualFp contra)
  decEq (FilePath xs x) (DirPath ys) = No fileNotDir
  decEq (DirPath xs) (FilePath ys x) = No (negEqSym fileNotDir)
  decEq (DirPath xs) (DirPath ys)= 
    case decEq xs ys of 
      (Yes prf) => Yes (dpEqFromCmps prf)
      (No contra) => No (cmpsNotEqualDp contra)

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
            
implementation Eq FSTree where 
  (FSNode x xs) == (FSNode y ys) = assert_total $ x == y && xs == ys
  (FSLeaf x) == (FSLeaf y) = x == y
  _ == _ = False
  
dirStr : List String -> String
dirStr [] = ""
dirStr (x :: xs) = x ++ "/" ++ dirStr xs  
  
implementation Show Path where 
  show (FilePath xs x) = 
    let str = 
      dirStr xs in 
    case str of 
      "" => x
      _  => str ++ "/" ++ x
  show (DirPath xs) = dirStr xs
  
nodeNotLeaf : FSNode x xs = FSLeaf y -> Void 
nodeNotLeaf Refl impossible

nameEqFromNodeEq : FSNode x xs = FSNode y ys -> x = y 
nameEqFromNodeEq Refl = Refl

recEqFromNodeEq : FSNode x xs = FSNode y ys -> xs = ys
recEqFromNodeEq Refl = Refl

nodeEq : x = y -> xs = ys -> FSNode x xs = FSNode y ys
nodeEq Refl Refl = Refl

nodeNameNotEq : (x = y -> Void) -> FSNode x xs = FSNode y ys -> Void
nodeNameNotEq contra = contra . nameEqFromNodeEq

nodeRecNotEq : (xs = ys -> Void) -> FSNode x xs = FSNode y ys -> Void 
nodeRecNotEq contra = contra . recEqFromNodeEq

nameEqFromLeafEq : FSLeaf x = FSLeaf y -> x = y 
nameEqFromLeafEq Refl = Refl

leafNameNotEq : (x = y -> Void) -> FSLeaf x = FSLeaf y -> Void
leafNameNotEq contra = contra . nameEqFromLeafEq

leafEq : x = y -> FSLeaf x = FSLeaf y
leafEq Refl = Refl
  
implementation DecEq FSTree where 
  decEq (FSNode x xs) (FSNode y ys) = assert_total $
    case decEq x y of 
      (Yes prf1) => 
        case decEq xs ys of 
          (Yes prf2) => Yes (nodeEq prf1 prf2)
          (No contra) => No (nodeRecNotEq contra)
      (No contra) => No (nodeNameNotEq contra)
  decEq (FSNode x xs) (FSLeaf y) = No nodeNotLeaf
  decEq (FSLeaf x) (FSNode y xs) = No (negEqSym nodeNotLeaf)
  decEq (FSLeaf x) (FSLeaf y) =
    case decEq x y of 
      (Yes prf) => Yes (leafEq prf)
      (No contra) => No (leafNameNotEq contra)

data FSElem : Path -> FSTree -> Type where 
  HereDir  : FSElem (DirPath []) 
                    (FSNode x xs)
  HereFile : (n1 = n2) -> FSElem (FilePath [] n1) 
                                 (FSLeaf (MkFileInfo n2 md)) 
  ThereDir : (fs : FSTree) -> FSElem (DirPath xs) fs 
                           -> Elem fs ys -> (n : String) 
                           -> FSElem (DirPath (n :: xs)) 
                                     (FSNode (MkFileInfo n md) ys)
  ThereFile : (fs : FSTree) -> FSElem (FilePath xs x) fs 
                            -> Elem fs ys -> (n : String)
                            -> FSElem (FilePath (n :: xs) x) 
                                      (FSNode (MkFileInfo n md) ys)

castFS : fs1 = fs2 -> FSElem p fs1 -> FSElem p fs2
castFS Refl x = x

castFS' : fs1 = fs2 -> Data.List.Elem fs1 xs -> Data.List.Elem fs2 xs
castFS' Refl x = x

TdFsEq : ThereDir fs1 x1 y1 prf1 
         = ThereDir fs2 x2 y2 prf2 -> fs1 = fs2
TdFsEq Refl = Refl

TfFsEq : ThereFile fs1 x1 y1 prf1
         = ThereFile fs2 x2 y2 prf2 -> fs1 = fs2
TfFsEq Refl = Refl

TdFsNotEqual : (fs1 = fs2 -> Void) -> 
                 ThereDir fs1 x1 y1 prf1 
                 = ThereDir fs2 x2 y2 prf2 -> Void
TdFsNotEqual contra = contra . TdFsEq

TfFsNotEqual : (fs1 = fs2 -> Void) -> 
               ThereFile fs1 x1 y1 prf1
               = ThereFile fs2 x2 y2 prf2 -> Void
TfFsNotEqual contra = contra . TfFsEq

TdRecEq : ThereDir fs1 x1 y1 prf1 
          = ThereDir fs1 x2 y2 prf2 -> x1 = x2
TdRecEq Refl = Refl 

TfRecEq : ThereFile fs1 x1 y1 prf1
          = ThereFile fs1 x2 y2 prf2 -> x1 = x2
TfRecEq Refl = Refl

TdElemEq : ThereDir fs1 x1 y1 prf1 
           = ThereDir fs1 x2 y2 prf -> y1 = y2
TdElemEq Refl = Refl

TfElemEq : ThereFile fs1 x1 y1 prf1
           = ThereFile fs1 x2 y2 prf -> y1 = y2
TfElemEq Refl = Refl

TdRecNotEqual : (fsprf : fs1 = fs2) -> (castFS fsprf x1 = x2 -> Void) 
                                    -> ThereDir fs1 x1 y1 prf1 
                                       = ThereDir fs2 x2 y2 prf2 -> Void
TdRecNotEqual Refl contra = contra . TdRecEq

TfRecNotEqual : (fsprf : fs1 = fs2) -> (castFS fsprf x1 = x2 -> Void)
                                    -> ThereFile fs1 x1 y1 prf1
                                       = ThereFile fs2 x2 y2 prf2 -> Void
TfRecNotEqual Refl contra = contra . TfRecEq

TdElemNotEqual : (fsprf : fs1 = fs2) -> ((castFS' fsprf y1) = y2 -> Void) 
                                     -> ThereDir fs1 x1 y1 prf1 
                                        = ThereDir fs2 x2 y2 prf2 -> Void
TdElemNotEqual Refl contra = contra . TdElemEq

TfElemNotEqual : (fsprf : fs1 = fs2) -> ((castFS' fsprf y1) = y2 -> Void)
                                     -> ThereFile fs1 x1 y1 prf1
                                        = ThereFile fs2 x2 y2 prf2 -> Void
TfElemNotEqual Refl contra = contra . TfElemEq

TdEq :(p1 : fs1 = fs2) -> (p2 : castFS p1 x1 = x2) 
                       -> (p3 : castFS' p1 y1 = y2) 
                       -> (p4 : n1 = n2) 
                       -> ThereDir {md=md} fs1 x1 y1 n1 
                          = ThereDir {md=md} fs2 x2 y2 n2
TdEq Refl Refl Refl Refl = Refl

TfEq : (p1 : fs1 = fs2) -> (p2 : castFS p1 x1 = x2)
                        -> (p3 : castFS' p1 y1 = y2)
                        -> (p4 : n1 = n2)
                        -> ThereFile {md=md} fs1 x1 y1 n1
                           = ThereFile {md=md} fs2 x2 y2 n2
TfEq Refl Refl Refl Refl = Refl
                              
implementation DecEq (FSElem p fs) where 
  decEq HereDir HereDir = Yes Refl
  decEq (HereFile Refl) 
        (HereFile Refl) = 
    Yes Refl
  decEq (ThereDir fs1 x y _) 
        (ThereDir fs2 z w _) = 
    case decEq fs1 fs2 of 
      (Yes prf1) => 
        case decEq 
          (castFS prf1 x) z of 
          (Yes prf2) => 
            case decEq 
              (castFS' prf1 y) w of 
              (Yes prf3) => 
                Yes (TdEq prf1 prf2 prf3 Refl)
              (No contra) => 
                No (TdElemNotEqual prf1 contra)
          (No contra) => 
            No (TdRecNotEqual prf1 contra)
      (No contra) => 
        No (TdFsNotEqual contra)
  decEq (ThereFile fs1 y z _) 
        (ThereFile fs2 x w _) = 
    case decEq fs1 fs2 of
      (Yes prf1) => 
        case decEq
          (castFS prf1 y) x of
          (Yes prf2) => 
            case decEq
              (castFS' prf1 z) w of
              (Yes prf3) => 
                Yes (TfEq prf1 prf2 prf3 Refl)
              (No contra) => 
                No (TfElemNotEqual prf1 contra)
          (No contra) => 
            No (TfRecNotEqual prf1 contra)
      (No contra) => 
        No (TfFsNotEqual contra)
