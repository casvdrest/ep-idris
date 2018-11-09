module AtomicProofs

import Environment
import Data.So
import Data.List
import Syntax

||| A proof that some element of a vector satisfies some property
|||
||| @ P the property to be satsified
data Any : (P : a -> Type) -> List a -> Type where
  ||| A proof that the satisfying element is the first one in the `Vect`
  Here  : {P : a -> Type} -> {xs : List a} -> P x -> Any P (x :: xs)
  
  ||| A proof that the satsifying element is in the tail of the `Vect`
  There : {P : a -> Type} -> {xs : List a} -> Any P xs -> Any P (x :: xs)

||| No element of an empty vector satisfies any property
anyNilAbsurd : {P : a -> Type} -> Any P [] -> Void
anyNilAbsurd (Here _) impossible
anyNilAbsurd (There _) impossible  
  
implementation Uninhabited (Any p Nil) where
  uninhabited = anyNilAbsurd

||| Eliminator for `Any`
anyElim : {xs : List a} -> {P : a -> Type} -> (Any P xs -> b) -> (P x -> b) -> Any P (x :: xs) -> b
anyElim _ f (Here p) = f p
anyElim f _ (There p) = f p

||| Given a decision procedure for a property, determine if an element of a
||| vector satisfies it.
|||
||| @ P the property to be satisfied
||| @ dec the decision procedure
||| @ xs the vector to examine
total
any' : {P : a -> Type} -> (dec : (x : a) -> Dec (P x)) -> (xs : List a) -> Dec (Any P xs)
any' _ Nil = No anyNilAbsurd
any' p (x::xs) with (p x)
  | Yes prf = Yes (Here prf)
  | No prf =
    case any' p xs of
      Yes prf' => Yes (There prf')
      No prf' => No (anyElim prf' prf)

valueFromAny : {P : a -> Type} -> {xs : List a} -> Any P xs -> (a >< P)
valueFromAny {xs = (x :: _)}  (Here y)  = (x ** y)
valueFromAny {xs = (_ :: ys)} (There y) = valueFromAny y 

valueFromElem : {x : a} -> Elem x xs -> a >< (\v => v = x)
valueFromElem {x} _ = (x ** Refl)

total 
catRights : List (Either a b) -> List a
catRights [] = []
catRights ((Left l) :: xs) = l :: catRights xs
catRights ((Right r) :: xs) = catRights xs

total
isLeft : {a : Type} -> (v : Either a b) -> Type 
isLeft {a} v = (a >< \x => v = Left x)

total 
isRight : {b : Type} -> (v : Either a b) -> Type 
isRight {b} v = (b >< \x => v = Right x)

leftNotRight : Right r = Left l -> Void 
leftNotRight Refl impossible

decideLeft : {a : Type} -> {b : Type} -> (v : Either a b) -> Dec (isLeft v)
decideLeft {a = a} (Left l) = Yes (l ** Refl)
decideLeft {a = a} (Right r) = No ((\(_ ** prf) => leftNotRight prf))

||| Given a list, construct a proof for each element that
||| it is in fact in the list
elemProofs : (xs : List a) -> List (a >< (\x => Elem x xs))
elemProofs [] = []
elemProofs (x :: xs) = 
  let rec = 
    elemProofs xs in
  (x ** Here) :: (map (\(y ** prf) => (y ** There prf)) rec)  
  
postulate leneq_tail_equal : length (x :: xs) = length (y :: ys) -> length xs = length ys
postulate elemProofsPreservesLength : {xs : List a} -> List.length (elemProofs xs) = length xs

total rec_prf_ty : List FSTree -> Path -> (Path, FSTree) -> Type 
rec_prf_ty xs p1 (p2,fs) = ((FSElem p2 fs, Elem fs xs), p1 = p2)

total rec_contra_ty : List FSTree -> Path -> FSTree -> Type 
rec_contra_ty xs p fs = (FSElem p fs -> Void, Elem fs xs) 

filepath_pointsTo_node : FSElem (FilePath [] x) (FSNode y xs) -> Void
filepath_pointsTo_node _ impossible

filepath_fname_neq : (n1 = n2 -> Void) -> 
  FSElem (FilePath [] n1) (FSLeaf (MkFileInfo n2 md)) -> Void
filepath_fname_neq contra (HereFile prf) = contra prf

cmpeq_from_ThereFile : FSElem (FilePath (n1 :: xs) x) 
                              (FSNode (MkFileInfo n2 md) ys) -> n1 = n2
cmpeq_from_ThereFile (ThereFile fs x y n1) = Refl

filepath_cmpname_neq : (n1 = n2 -> Void) -> 
  FSElem (FilePath (n1 :: xs) x) (FSNode (MkFileInfo n2 md) ys) -> Void
filepath_cmpname_neq contra  = contra . cmpeq_from_ThereFile

filepath_cmpNonEmpty_pointsTo_leaf : FSElem (FilePath (x :: xs) name) (FSLeaf fi) -> Void
filepath_cmpNonEmpty_pointsTo_leaf _ impossible

dirpath_pointsTo_leaf : FSElem (DirPath xs) (FSLeaf x) -> Void
dirpath_pointsTo_leaf _ impossible

cmpeq_from_ThereDir : FSElem (DirPath (n1 :: xs)) 
                             (FSNode (MkFileInfo n2 md) ys) -> n1 = n2
cmpeq_from_ThereDir (ThereDir fs x y n1) = Refl

dirpath_cmpname_neq : (n1 = n2 -> Void) ->
  FSElem (DirPath (n1 :: xs)) (FSNode (MkFileInfo n2 md) ys) -> Void
dirpath_cmpname_neq contra = contra . cmpeq_from_ThereDir

not_in_sublist : {P : a -> Type} -> (Any P (x::xs) -> Void) -> Any P xs -> Void 
not_in_sublist contra = contra . There

total
lemma_fromright : {a : Type} -> {b : Type} -> 
                  (x : Either a b) -> {xs : List (Either a b)} 
                                   -> (Any AtomicProofs.isLeft xs -> Void) 
                                   -> Elem x xs 
                                   -> AtomicProofs.isRight x
lemma_fromright (Left l) contra Here = void (contra (Here (l ** Refl)))
lemma_fromright (Right r) contra Here = (r ** Refl)
lemma_fromright x contra (There later) = 
  lemma_fromright x (not_in_sublist contra) later             

total
fs_from_rec : {p : Path} -> {ys : List FSTree} -> 
              Either (((Path, FSTree) >< rec_prf_ty ys p)) 
                     (FSTree >< rec_contra_ty ys p) -> FSTree
fs_from_rec (Left (x ** pf)) = snd x
fs_from_rec (Right r) = fst r

lemma_lift_elem : {xs : List a} -> {ys : List b} -> length xs = length ys 
                                -> Elem x xs 
                                -> b >< (\y => Elem y ys)
lemma_lift_elem {ys = []} Refl Here impossible
lemma_lift_elem {ys = (x :: xs)} prf Here = (x ** Here)
lemma_lift_elem {ys = []} Refl (There _) impossible
lemma_lift_elem {xs = (x :: xs)} {ys = (y :: ys)} prf (There later) = 
  let (v ** pf) = lemma_lift_elem (leneq_tail_equal prf) later in (v ** There pf)
                  
g : {xs : List FSTree} -> {p : Path} -> 
    ((p : Path) -> (fs : FSTree) -> Dec (FSElem p fs)) -> 
    (FSTree >< \x => Elem x xs) -> Either (((Path, FSTree) >< rec_prf_ty xs p))
                                          (FSTree >< rec_contra_ty xs p)
g {p} f (y ** prf) = 
  case f p y of 
    (Yes pf) => Left ((p, y) ** ((pf, prf), Refl))
    (No contra) => Right (y ** (contra, prf))

||| Recursively search for proof on a list of FileSystem trees
total
recurse : {xs : List FSTree} -> (p : Path)
                             -> (lst : List (FSTree >< (\x => Elem x xs))) 
                             -> ((p : Path) -> (fs : FSTree) 
                                            -> Dec (FSElem p fs))
                             -> List (Either (((Path, FSTree) >< rec_prf_ty xs p))
                                               (FSTree >< rec_contra_ty xs p))
recurse {xs} p lst f = map (g f) lst
               
to_contra_dir : {ys : List FSTree} -> 
            {zs : List (Either (DPair (Path, FSTree) (rec_prf_ty ys (DirPath xs))) 
                               (FSTree >< rec_contra_ty ys (DirPath xs)))} ->  
            (Any AtomicProofs.isLeft zs -> Void) -> 
            (v : (Either (DPair (Path, FSTree) (rec_prf_ty ys (DirPath xs))) 
                         (FSTree >< rec_contra_ty ys (DirPath xs))) >< (\x => Elem x zs)) -> 
            FSElem (DirPath xs) (fs_from_rec (fst v)) -> Void
to_contra_dir {ys} {zs} contra (x ** y) prf with (lemma_fromright {xs=zs} x contra y)
  to_contra_dir {ys = ys} {zs = zs} contra 
            ((Right (fs ** (ctr, elem))) ** y) prf | 
              ((fs ** (ctr,elem)) ** Refl) = ctr prf
              
to_contra_file : {ys : List FSTree} -> 
                 {zs : List (Either (DPair (Path, FSTree) (rec_prf_ty ys (FilePath xs name))) 
                                    (FSTree >< rec_contra_ty ys (FilePath xs name)))} ->  
                 (Any AtomicProofs.isLeft zs -> Void) -> 
                 (v : (Either (DPair (Path, FSTree) (rec_prf_ty ys (FilePath xs name))) 
                              (FSTree >< rec_contra_ty ys (FilePath xs name))) 
                                >< (\x => Elem x zs)) -> 
                 FSElem (FilePath xs name) (fs_from_rec (fst v)) -> Void
to_contra_file {ys} {zs} contra (x ** y) prf with (lemma_fromright {xs=zs} x contra y)
  to_contra_file {ys = ys} {zs = zs} contra 
    ((Right (fs ** (ctr, elem))) ** y) prf | 
      ((fs ** (ctr,elem)) ** Refl) = ctr prf

fseq_rwr : fs1 = fs2 -> FSElem p fs1 -> FSElem p fs2
fseq_rwr Refl x = x

mutual 
  ||| Yields either a prove that the given path exists in the provided filesystem, 
  ||| or nothing if the latter is not the case
  export total provePathExists : (p : Path) -> (fs : FSTree) 
                                            -> Dec (FSElem p fs)
  
  -- A filepath that ends in a node does not exist
  provePathExists (FilePath [] x) 
                   (FSNode y xs) = No (filepath_pointsTo_node)
                  
  -- A filepath that ends in a leaf exists iff the name of the file 
  -- in the leaf is equal to the filename in the filepath.                 
  provePathExists (FilePath [] x) 
                  (FSLeaf (MkFileInfo name md)) 
                  with (decEq x name) 
                  
    -- Filenames equal, hence the file exists
    provePathExists (FilePath [] x) 
                    (FSLeaf (MkFileInfo name md)) 
                      | (Yes prf) = Yes (HereFile prf)
                      
    -- Filenames not equal, file does not exist
    provePathExists (FilePath [] x) 
                    (FSLeaf (MkFileInfo name md)) 
                      | (No contra) = No (filepath_fname_neq contra)
                      
  -- A filepath that passes through a node exists in the filesystem if: 
  --   a) The head of the component list equals the filename stored 
  --      in the node 
  --   b) A path that has the tail as its component list exists in one of 
  --      the children of the node
  provePathExists (FilePath (y :: xs) x) 
                  (FSNode (MkFileInfo name md) ys) 
                    with (decEq y name)
    
    -- Condition (a) is true, so we recurse on the children 
    -- of the node
    provePathExists (FilePath (name :: xs) x) 
                    (FSNode (MkFileInfo name md) ys) 
                      | (Yes Refl) = assert_total $
      case any' {P=isLeft} decideLeft (map (g {p=(FilePath xs x)} provePathExists) (elemProofs ys)) of
         (Yes prf) =>  
           case valueFromAny prf of 
             (_ ** (((FilePath xs x), fs) ** ((prf1, prf2), Refl)) ** _) => 
               Yes (ThereFile fs prf1 prf2 name)
         (No contra) => 
           let leneq = 
               (mapPreservesLength (g {p=(FilePath xs x)} provePathExists) (elemProofs ys)) in
           let leneq' = trans leneq (elemProofsPreservesLength {xs=ys}) in  
             No (lemma_file_contra {rec=(map (g {p=(FilePath xs x)} provePathExists) (elemProofs ys))} 
                {leneq=leneq'} contra)
    
    -- Condition (a) is false, hence the path does not exist
    provePathExists (FilePath (y :: xs) x) 
                    (FSNode (MkFileInfo name md) ys) 
                      | (No contra) = No (filepath_cmpname_neq contra)
  
  -- A filepath with a non-empty component list that ends in a leaf
  -- does not exist in the filesystem. 
  provePathExists (FilePath (y :: xs) x) 
                  (FSLeaf z) = No (filepath_cmpNonEmpty_pointsTo_leaf)
                  
  -- A directory path with an empty component list that ends in a node
  -- exists. 
  provePathExists (DirPath []) 
                  (FSNode x xs) = Yes HereDir
  
  -- A directory path with an empty component list that ends in a leaf
  -- does not exist.
  provePathExists (DirPath []) 
                  (FSLeaf x) = No (dirpath_pointsTo_leaf)
                  
  -- A directory path that passes through a node exists in the filesystem if: 
  --   a) The head of the component list equals the filename stored 
  --      in the node 
  --   b) A path that has the tail as its component list exists in one of 
  --      the children of the node 
  provePathExists (DirPath (x :: xs)) 
                  (FSNode (MkFileInfo name md) ys) 
                    with (decEq x name)
                    
    -- The head of the component list matches the filename stored in 
    -- the node, so we recurse
    provePathExists (DirPath (name :: xs)) 
                    (FSNode (MkFileInfo name md) ys) 
                      | (Yes Refl) = assert_total $ 
      case any' {P=isLeft} decideLeft (map (g {p=(DirPath xs)} provePathExists) (elemProofs ys)) of
         (Yes prf) =>  
           case valueFromAny prf of 
             (_ ** (((DirPath xs), fs) ** ((prf1, prf2), Refl)) ** _) => 
               Yes (ThereDir fs prf1 prf2 name)
         (No contra) => 
           let leneq = 
               (mapPreservesLength (g {p=(DirPath xs)} provePathExists) (elemProofs ys)) in
           let leneq' = trans leneq (elemProofsPreservesLength {xs=ys}) in  
             No (lemma_dir_contra {rec=(map (g {p=(DirPath xs)} provePathExists) (elemProofs ys))} 
                {leneq=leneq'} contra)
           
            
    -- The head of the component list does not correspond with the name 
    -- stored in the node, hence the path does not exist.
    provePathExists (DirPath (x :: xs)) 
                    (FSNode (MkFileInfo name md) ys) 
                      | (No contra) =  No (dirpath_cmpname_neq contra)
                      
  -- A directory path with a non-empty component list that 
   -- ends in a node does not exist in the filesystem. 
  provePathExists (DirPath (x :: xs)) 
                  (FSLeaf y) = No dirpath_pointsTo_leaf

  lemma_file_contra : {rec : List (Either (((Path, FSTree) >< rec_prf_ty ys (FilePath xs name)))
                                               (FSTree  >< rec_contra_ty ys (FilePath xs name)))} -> 
                     {leneq : length rec = length ys} -> 
                     (Any AtomicProofs.isLeft rec -> Void) ->
                     FSElem (FilePath (n::xs) name) (FSNode (MkFileInfo n md) ys) -> Void
  lemma_file_contra {ys} {xs} {leneq} contra 
    (ThereFile fs2 x y n) with ((lemma_file_conv {leneq=leneq} {fs=fs2} y))
    lemma_file_contra {ys} {xs} {leneq} contra (ThereFile fs x y n) | (rval  ** (elem, fseqprf)) = 
      to_contra_file {ys=ys} {xs=xs} contra (rval ** elem) (fseq_rwr fseqprf x)

  lemma_dir_contra : {rec : List (Either (((Path, FSTree) >< rec_prf_ty ys (DirPath xs)))
                                               (FSTree  >< rec_contra_ty ys (DirPath xs)))} -> 
                     {leneq : length rec = length ys} -> 
                     (Any AtomicProofs.isLeft rec -> Void) ->
                     FSElem (DirPath (n::xs)) (FSNode (MkFileInfo n md) ys) -> Void
  lemma_dir_contra {ys} {xs} {leneq} contra 
    (ThereDir fs2 x y n) with ((lemma_dir_conv {leneq=leneq} {fs=fs2} y))
    lemma_dir_contra {ys} {xs} {leneq} contra (ThereDir fs x y n) | (rval  ** (elem, fseqprf)) = 
      to_contra_dir {ys=ys} {xs=xs} contra (rval ** elem) (fseq_rwr fseqprf x)   
      
  lemma_dir_conv : {rec : List (Either (((Path, FSTree) >< rec_prf_ty ys (DirPath xs)))
                                               (FSTree  >< rec_contra_ty ys (DirPath xs)))} -> 
                   {leneq : length rec = length ys} -> 
                   {fs : FSTree} -> Elem fs ys -> 
                       (Either (((Path, FSTree) >< rec_prf_ty ys (DirPath xs)))
                               (FSTree  >< rec_contra_ty ys (DirPath xs)) 
                         >< (\rval => (Elem rval rec, fs = fs_from_rec rval)))
  lemma_dir_conv {ys} {rec} {fs} {leneq} elem 
                 with (lemma_lift_elem {xs=ys} {ys=rec} (sym leneq) elem) 
    lemma_dir_conv {ys = ys} {rec = rec} {fs = fs} elem | (x ** pf) = 
      (x ** (pf, believe_me ()))
      
  lemma_file_conv : {rec : List (Either (((Path, FSTree) >< rec_prf_ty ys (FilePath xs name)))
                                               (FSTree  >< rec_contra_ty ys (FilePath xs name)))} -> 
                   {leneq : length rec = length ys} -> 
                   {fs : FSTree} -> Elem fs ys -> 
                       (Either (((Path, FSTree) >< rec_prf_ty ys (FilePath xs name)))
                               (FSTree  >< rec_contra_ty ys (FilePath xs name)) 
                         >< (\rval => (Elem rval rec, fs = fs_from_rec rval)))
  lemma_file_conv {ys} {rec} {fs} {leneq} elem 
                 with (lemma_lift_elem {xs=ys} {ys=rec} (sym leneq) elem) 
    lemma_file_conv {ys = ys} {rec = rec} {fs = fs} elem | (x ** pf) = 
      (x ** (pf, believe_me ()))
