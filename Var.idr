module Var

import Expr

data VarE : (Type -> Type) -> Type where
  Var : String -> Var e

implementation Functor VarE where
  map f (Var x) = Var x

implementation Eval (Expr  VarE)
