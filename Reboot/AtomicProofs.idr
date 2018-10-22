module AtomicProofs

import Environment
import Syntax
import Data.So
import Data.List

||| intToBool (prim__eqString a a) != True according to idris, so 
||| this hack shall saviour us until further notice
total provePrimStrEq : {a : String} -> {b : String} -> a = b -> So (a == b)
provePrimStrEq Refl = believe_me Oh

total lemma_and : {l : Bool} -> {r : Bool} -> 
                  So l -> So r -> So (l && r)
lemma_and Oh Oh = Oh

total lemma_or_left : {r : Bool} -> {l : Bool} -> 
                      So l -> So (l || r)
lemma_or_left Oh = Oh

total lemma_or_sym : {r : Bool} -> {l : Bool} -> 
                     So (l || r) -> So (r || l)
lemma_or_sym {r = False} {l = False} Oh impossible
lemma_or_sym {r = False} {l = True} Oh = Oh
lemma_or_sym {r = True} {l = l} prf = Oh


total lemma_or_right : {r : Bool} -> {l : Bool} -> 
                       So r -> So (l || r)
lemma_or_right {l} {r = True} pf = 
  lemma_or_sym (lemma_or_left pf)

lemma_any : {p : FSTree -> Bool} -> {lst : List FSTree} -> 
            Elem x lst -> So (p x) -> So (any' p lst)
lemma_any {p} {lst = x :: xs} Here pf2a with (p x) 
  lemma_any {p = _} {lst = _ :: _} Here Oh | False impossible
  lemma_any {p = p} {lst = x :: xsa} Here Oh | True = Oh
lemma_any (There later) pf2a = 
  lemma_or_right (lemma_any later pf2a)


total lemma_fpath : {x : String} -> {name : String} -> 
                    {y : String} -> {ys : List String} ->
                    {xs : List FSTree} -> (md : FileMD) -> 
                    (name = x) -> asType (Atom (pathExists (FilePath ys y))) -> 
                    Maybe (So (
                      pathExists (FilePath (x :: ys) y) 
                      (FSNode (MkFileInfo name md) xs)))
lemma_fpath {x} {name} {y} {ys} {xs} 
            _ prf (val ** pf) with (isElem val xs)
  lemma_fpath {x = x} {name = name} 
              {y = y} {ys = ys} {xs = xs} 
              _ prf (val ** pf) | (Yes z) = 
    Just $ lemma_and 
      {l = (intToBool (prim__eqString name x))} 
      {r = any' (pathExists (FilePath ys y)) xs} 
      (provePrimStrEq prf) 
      (lemma_any z pf)
  lemma_fpath {x = x} {name = name} 
              {y = y} {ys = ys} {xs = xs} 
              _ prf (val ** pf) | (No contra) = Nothing
    
total lemma_dpath : {x : String} -> {name : String} -> 
                    {ys : List String}  -> {xs : List FSTree} -> 
                    (md : FileMD) -> (name = x) -> 
                    asType (Atom (pathExists (DirPath ys)))-> 
                    Maybe (So (
                      pathExists (DirPath (x :: ys)) 
                      (FSNode (MkFileInfo name md) xs)))
lemma_dpath {x} {name} {ys} {xs} 
            _ prf (val ** pf) with (isElem val xs)
  lemma_dpath {x} {name} {ys} {xs} 
              _ prf (val ** pf) | (Yes z) = 
    Just $ lemma_and 
      {l = (intToBool (prim__eqString name x))} 
      {r = any' (pathExists (DirPath ys)) xs} 
      (provePrimStrEq prf) 
      (lemma_any z pf)
  lemma_dpath {x} {name} {ys} {xs} 
              _ prf (val ** pf) | (No contra) = Nothing

export
total provePathExists : (fs : FSTree) -> (p : Path) -> 
                        Maybe ([[. FSTree .]] (Atom $ pathExists p))
provePathExists (FSNode (MkFileInfo name md) xs) (FilePath [] y) 
  = Nothing
provePathExists (FSNode (MkFileInfo name md) xs) 
                (FilePath (x :: ys) y) with (decEq name x) 
  provePathExists (FSNode (MkFileInfo name md) xs) 
                  (FilePath (x :: ys) y) | (Yes prf1) = assert_total $
    do prf2 <- ( listToMaybe . 
                 catMaybes . 
                 map (\fs => provePathExists fs (FilePath ys y))
               ) xs
       prf3 <- lemma_fpath {x=x} {name=name} 
                           md prf1 prf2
       pure ((FSNode 
               (MkFileInfo name md) xs) ** prf3
            )
  provePathExists (FSNode (MkFileInfo name md) xs) 
                  (FilePath (x :: ys) y) | (No contra) = Nothing
provePathExists (FSNode x xs) (DirPath []) 
  = Just (FSNode x xs ** Oh)
provePathExists (FSNode (MkFileInfo name md) xs) 
                (DirPath (y :: ys)) with (decEq name y)
  provePathExists (FSNode (MkFileInfo name md) xs) 
                  (DirPath (y :: ys)) | (Yes prf1) = assert_total $ 
    do prf2 <- ( listToMaybe . 
                 catMaybes . 
                 map (\fs => provePathExists fs (DirPath ys))
               ) xs
       prf3 <- lemma_dpath {x=y} {name=name} 
                           {xs=xs} md prf1 prf2
       pure ((FSNode 
               (MkFileInfo name md) xs) ** prf3
            )
  provePathExists (FSNode (MkFileInfo name md) xs) 
                          (DirPath (y :: ys)) | (No contra) = Nothing
provePathExists (FSLeaf (MkFileInfo name md)) 
                (FilePath [] y) with (decEq y name)
  provePathExists (FSLeaf (MkFileInfo name md)) 
                  (FilePath [] y) | No _ = Nothing
  provePathExists (FSLeaf (MkFileInfo name md)) 
                  (FilePath [] y) | Yes prf = Just 
    ((FSLeaf (MkFileInfo name md)) ** 
             (provePrimStrEq prf))
provePathExists (FSLeaf x) (FilePath (z :: xs) y) = Nothing
provePathExists (FSLeaf x) (DirPath xs) = Nothing
