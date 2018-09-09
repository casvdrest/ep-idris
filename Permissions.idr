module Permissions

import Data.Vect

public export
Name : Type
Name = String

public export
User : Type
User = Pair Name Name

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


infix 10 <?

export
(<?) : Permission -> FMod -> Bool
[rp,_,_] <? R = rp
[_,wp,_] <? W = wp
[_,_,xp] <? X = xp

public export
data FileMD = MkFileMD FType FPermission User
public export
data FileInfo = MkFileInfo String FileMD

pOwner : FPermission -> Permission
pOwner [ow,_,_] = ow

pGroup : FPermission -> Permission
pGroup [_,gr,_] = gr

pOther : FPermission -> Permission
pOther [_,_,ot] = ot

modAllowed : FMod -> User -> FileMD -> Bool
modAllowed mod (uname, ugroup) (MkFileMD _ fperm (fowner, fgroup)) =
  (uname == fowner  && ((pOwner fperm) <? mod)) ||
  (ugroup == fgroup && ((pGroup fperm) <? mod)) ||
  ((pOther fperm) <? mod)

canRead : User -> FileMD -> Bool
canRead = modAllowed R

canWrite : User -> FileMD -> Bool
canWrite = modAllowed W

canExecute : User -> FileMD -> Bool
canExecute = modAllowed X
