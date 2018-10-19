module Syntax 

-- File system data types
import Environment

import Data.So

infixl 5 /\
infixl 4 :=>
infix  6 =:=

infixl 7 <#>

%access public export

interface Contravariant (f : Type -> Type) where
  (<#>) : (b -> a) -> f a -> f b

data Predicate : Type -> Type where 
  (/\)  : Predicate s -> Predicate s -> Predicate s
  (:=>) : Predicate s -> Predicate s -> Predicate s
  (=:=) : (DecEq a) => a -> a -> Predicate s
  Forall : (a : Type) -> (a -> Predicate s) -> Predicate s
  --Exists : (a : Type) -> (a -> Predicate s) -> Predicate s
  StPred : (s -> Bool) -> Predicate s
  T : Predicate s
  F : Predicate s
  
implementation Contravariant Predicate where 
  f <#> (p /\ q)  = f <#> p /\ f <#> q
  f <#> (p :=> q) = f <#> p :=> f <#> q
  f <#> (a =:= b) = a =:= b
  f <#> (Forall ty g) = Forall ty ((<#>) f . g)
  --f <#> (Exists ty g) = Exists ty ((<#>) f . g)
  f <#> (StPred g) = StPred (g . f)
  f <#> T = T
  f <#> F = F
  
infix 1 ><

||| Constructs a dependent pair
(><) : (a : Type) -> (a -> Type) -> Type
a >< b = DPair a b

total
tyFromBool : Bool -> Type 
tyFromBool True = Unit
tyFromBool False = Void

total
asType : Predicate s -> (s -> Type) 
asType (p /\ q)  = (\s => (asType p s, asType q s))
asType (p :=> q)  = (\s => asType p s -> asType q s)
asType (a =:= b)  = (\s => (a = b))
asType (Forall ty p) = (\s => ((x : ty) -> asType (p x) s))
--asType (Exists ty p) = (\s => (ty >< (\x => asType (p x) s)))
asType (StPred f) = (\s => tyFromBool (f s)) 
asType T          = (\s => Unit) 
asType F          = (\s => Void)

syntax "[[..]]" [pred] = asType pred
  
data Cmd next = Ls Path (List Path -> next) 
                | Cat Path (String -> next)
                | Echo String (String -> next)
                | Return
 
||| Create a predicate that asserts whether the input path is valid in 
||| the filesystem.
total
pathExists : Path -> Predicate FSTree 
pathExists (DirPath []) =
  StPred (\fs => 
    case fs of 
      (FSLeaf _) => False
      (FSNode _ _) => True
   )
pathExists (DirPath (x :: xs)) = assert_total $
  StPred (\fs => 
    case fs of
      (FSLeaf _) => False
      (FSNode (MkFileInfo name _) remainder) => 
          case x == name of 
            True => 
              case any 
                (\fs =>
                   case pathExists (DirPath xs) of 
                     (StPred f) => f fs
                     _ => False
                ) remainder of 
                True   => True
                False  => False
            False => False
  ) 
pathExists (FilePath [] name) = 
  StPred (\fs => 
    case fs of 
      (FSNode _ _) => False
      (FSLeaf (MkFileInfo name' _)) => name' == name
  )
pathExists (FilePath (x :: xs) name) = assert_total $ 
  StPred (\fs => 
    case fs of 
      (FSNode (MkFileInfo dname _) remainder) => 
        case x == dname of 
          True => 
            case any 
              (\fs =>
                 case pathExists (FilePath xs name) of 
                   (StPred f) => f fs
                   _ => False
              ) remainder of 
              True   => True
              False  => False
          False => False
      (FSLeaf _) => False
  )

{-
pre : Cmd a next -> Predicate FSTree
pre (Ls p cmd)   = pathExists p /\ Forall (List Path) (\lst => pre (cmd lst))
pre (Cat p cmd)  = pathExists p /\ Forall String (\str => pre (cmd str))
pre (Echo s cmd) = Forall String (\str => pre (cmd str))
pre (Return x)   = T
-}

assertPre : (pre : Predicate FSTree) -> (fs : FSTree) -> Maybe (([[..]] pre) fs)
assertPre (x /\ y) fs = do 
  pure (!(assertPre x fs), !(assertPre y fs))
assertPre (x :=> y) fs = do 
  x' <- assertPre x fs 
  y' <- assertPre y fs 
  pure (const y')
assertPre (x =:= y) fs = 
  case decEq x y of 
    (Yes prf) => pure prf
    (No contra) => Nothing
assertPre (Forall a f) fs = pure $ (\val => (\(Just x) => x) (assertPre (f val) fs))
--assertPre (Exists a f) fs = ?ap_hole5
assertPre (StPred f) fs with (f fs) 
  assertPre (StPred f) fs | False = Nothing
  assertPre (StPred f) fs | True = pure ()
assertPre F fs = Nothing 



 
 
 
                                     
