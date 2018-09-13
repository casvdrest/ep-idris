module Permissions

import Data.Vect

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
