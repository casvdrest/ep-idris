module AtomicProofs

import Environment
import Data.So
import Data.List
import Syntax

total 
catRights : List (Either a b) -> List a
catRights [] = []
catRights ((Left l) :: xs) = l :: catRights xs
catRights ((Right r) :: xs) = catRights xs

pushPf : String -> (p : Path) -> (p = (FilePath xs x)) -> Path
pushPf x (FilePath xs y) Refl = FilePath (x :: xs) y
pushPf _ (DirPath _) Refl impossible

pushPd : String -> (p : Path) -> (p = (DirPath xs)) -> Path
pushPd x (DirPath xs) Refl = DirPath (x :: xs)
pushPd y (FilePath _ _) Refl impossible

||| Given a list, construct a proof for each element that
||| it is in fact in the list
elemProofs : (xs : List a) -> List (a >< (flip Elem) xs)
elemProofs [] = []
elemProofs (x :: xs) = 
  let rec = 
    elemProofs xs in
  (x ** Here) :: (map (\(y ** prf) => (y ** There prf)) rec)  

total rec_prf_ty : List FSTree -> Path -> (Path, FSTree) -> Type 
rec_prf_ty xs p1 (p2,fs) = ((FSElem p2 fs, Elem fs xs), p1 = p2)

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

lemma_rec_all_neg_dir : {fs : FSTree} -> (ys : List (Either 
                                           (((Path, FSTree) >< rec_prf_ty xs p))
                                           ((FSTree >< (\fs => FSElem p fs -> Void)))))
                                      -> (Elem y ys -> y = Right contra)
                                      -> (p : Path) 
                                      -> Elem fs xs 
                                      -> (FSElem p fs -> Void)


lemma_rec_not_found_dir : {md : FileMD} -> (name : String) 
                                    -> (p : Path) 
                                    -> (prf : p = (DirPath cmps))
                                    -> (xs : List FSTree) 
                                    -> ({fs : FSTree} -> Elem fs xs -> (FSElem p fs -> Void))
                                    -> FSElem (pushPd name p prf) 
                                              (FSNode (MkFileInfo name md) xs) -> Void
lemma_rec_not_found_dir name (DirPath cmps) Refl xs f 
                             (ThereDir fs prf_rec prf_elem name) = f prf_elem prf_rec

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
                      | (Yes Refl) = ?hole {-  assert_total $
       case  ( listToMaybe 
             . catMaybes
             . recurse {xs=ys} (FilePath xs x)
             ) (elemProofs ys) of
         Nothing => ?hole_1
         (Just (((FilePath xs x), fs) ** ((prf1, prf2), Refl))) => 
           Yes (ThereFile fs prf1 prf2 name)
           -}
    
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
      let rec =
        recurse {xs = ys} (DirPath xs) (elemProofs ys) in 
      case catRights rec of
         [] => 
           No ( lemma_rec_not_found_dir name 
                (DirPath (xs)) Refl ys 
                (lemma_rec_all_neg_dir 
                  rec ?lemma
                  (DirPath xs))) 
          {-
         (Just (((DirPath xs), fs) ** 
           ((prf1, prf2), Refl))) => 
             Yes (ThereDir fs prf1 prf2 name) -}
            
    -- The head of the component list does not correspond with the name 
    -- stored in the node, hence the path does not exist.
    provePathExists (DirPath (x :: xs)) 
                    (FSNode (MkFileInfo name md) ys) 
                      | (No contra) =  No (dirpath_cmpname_neq contra)
                      
  -- A directory path with a non-empty component list that 
  -- ends in a node does not exist in the filesystem. 
  provePathExists (DirPath (x :: xs)) 
                  (FSLeaf y) = No dirpath_pointsTo_leaf
  
  ||| Recursively search for proof on a list of FileSystem trees
  ||| TODO: pair Elem proof with FSElem proofs to prevent spurious 
  ||| call to isElem in recursive cases of provePathExists. 
  recurse : {xs : List FSTree} -> (p : Path)
                               -> (lst : List (FSTree >< (flip Elem) xs)) 
                               -> List (Either (((Path, FSTree) >< rec_prf_ty xs p))
                                  ((FSTree >< (\fs => FSElem p fs -> Void))))
  recurse p [] = []
  recurse p ((x ** prf) :: xs) with (provePathExists p x)
  
    -- The child does not contain the path, so we return nothing
    recurse p ((x ** prf) :: xs) | No contra = 
      Right (x ** contra) :: recurse p xs
      
     -- Child contains the path, yield appropriate proof
    recurse p ((x ** prf) :: xs) | (Yes y) = 
     Left ((p, x) ** ((y, prf), Refl)) :: recurse p xs
