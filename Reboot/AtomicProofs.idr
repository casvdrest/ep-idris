module AtomicProofs

import Environment
import Data.So
import Data.List
import Syntax

||| Given a list, construct a proof for each element that
||| it is in fact in the list
elemProofs : (xs : List a) -> List (a >< (flip Elem) xs)
elemProofs [] = []
elemProofs (x :: xs) = 
  let rec = 
    elemProofs xs in
  (x ** Here) :: (map (\(y ** prf) => (y ** There prf)) rec)  

total rec_prf_ty : List FSTree -> (Path, FSTree) -> Type 
rec_prf_ty xs (p,fs) = (FSElem p fs, Elem fs xs)

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
                      | (Yes Refl) = ?hole {-assert_total $ do
      ((path, fs) ** (prf, prf_elem)) <- 
        ( listToMaybe 
        . catMaybes
        . recurse {xs=ys} (FilePath xs x)
        ) (elemProofs ys)
      case path of
        (DirPath xs) => ?hole
        (FilePath xs' x') => 
          case decEq xs xs' of 
            (Yes Refl) => 
              case decEq x x' of 
                (Yes Refl) => 
                  Just (ThereFile fs prf prf_elem name)
                (No contra) => ?hole
            (No contra) => ?hole -}
    
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
                      | (Yes Refl) = ?hole {-assert_total $ do
      ((path, fs) ** (prf, prf_elem)) <- 
        ( listToMaybe 
        . catMaybes
        . recurse (DirPath xs)
        ) (elemProofs ys)
      case path of
        (FilePath xs x) => ?hole
        (DirPath xs') => 
          case decEq xs xs' of 
            (Yes Refl) => 
              Just (ThereDir fs prf prf_elem name)
            (No contra) => ?hole -}
            
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
                               -> List (Dec ((Path, FSTree) >< rec_prf_ty xs))
  recurse p [] = []
  recurse {xs} p ((x ** prf) :: xs') with (provePathExists p x)
  
    -- The child does not contain the path, so we yield a contra-proof
    recurse {xs} p ((x ** prf) :: xs') | No contra = 
      No ?contraprf :: recurse {xs=xs} p xs'
      
     -- Child contains the path, yield appropriate proof
    recurse {xs} p ((x ** prf) :: xs') | (Yes y) = 
      Yes ((p, x) ** (y, prf)) :: recurse p xs'
   
 
