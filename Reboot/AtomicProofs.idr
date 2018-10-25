module AtomicProofs

import Environment
import Data.So
import Data.List
import Syntax
  
mutual 
  ||| Yields either a prove that the given path exists in the provided filesystem, 
  ||| or nothing if the latter is not the case
  export total provePathExists : (p : Path) -> (fs : FSTree) -> Maybe (FSElem p fs)
  
  ||| A filepath that ends in a node does not exist
  provePathExists (FilePath [] x) 
                  (FSNode y xs) = Nothing
                  
  ||| A filepath that ends in a leaf exists iff the name of the file 
  ||| in the leaf is equal to the filename in the filepath.                 
  provePathExists (FilePath [] x) 
                  (FSLeaf (MkFileInfo name md)) 
                  with (decEq x name) 
                  
    ||| Filenames equal, hence the file exists
    provePathExists (FilePath [] x) 
                    (FSLeaf (MkFileInfo name md)) 
                      | (Yes prf) = Just (HereFile prf)
                      
    ||| Filenames not equal, file does not exist
    provePathExists (FilePath [] x) 
                    (FSLeaf (MkFileInfo name md)) 
                      | (No contra) = Nothing
                      
  ||| A filepath that passes through a node exists in the filesystem if: 
  |||   a) The head of the component list equals the filename stored 
  |||      in the node 
  |||   b) A path that has the tail as its component list exists in one of 
  |||      the children of the node
  provePathExists (FilePath (y :: xs) x) 
                  (FSNode (MkFileInfo name md) ys) 
                    with (decEq y name)
    
    ||| Condition (a) is true, so we recurse on the children 
    ||| of the node
    provePathExists (FilePath (name :: xs) x) 
                    (FSNode (MkFileInfo name md) ys) 
                      | (Yes Refl) = assert_total $ do
      ((path, fs) ** prf) <- 
        ( listToMaybe 
        . catMaybes
        . recurse (FilePath xs x)
        ) ys
      case path of
        (DirPath xs) => Nothing
        (FilePath xs' x') => 
          case decEq xs xs' of 
            (Yes Refl) => 
              case decEq x x' of 
                (Yes Refl) => 
                  case isElem fs ys of 
                    (Yes prf_elem) => 
                      Just (ThereFile fs prf prf_elem name)
                    (No contra) => Nothing 
                (No contra) => Nothing
            (No contra) => Nothing
    
    ||| Condition (a) is false, hence the path does not exist
    provePathExists (FilePath (y :: xs) x) 
                    (FSNode (MkFileInfo name md) ys) 
                      | (No contra) = Nothing
  
  ||| A filepath with a non-empty component list that ends in a leaf
  ||| does not exist in the filesystem. 
  provePathExists (FilePath (y :: xs) x) 
                  (FSLeaf z) = Nothing
                  
  ||| A directory path with an empty component list that ends in a node
  ||| exists. 
  provePathExists (DirPath []) 
                  (FSNode x xs) = Just HereDir
  
  ||| A directory path with an empty component list that ends in a node
  ||| does not exist.
  provePathExists (DirPath []) 
                  (FSLeaf x) = Nothing
                  
  ||| A directory path that passes through a node exists in the filesystem if: 
  |||   a) The head of the component list equals the filename stored 
  |||      in the node 
  |||   b) A path that has the tail as its component list exists in one of 
  |||      the children of the node 
  provePathExists (DirPath (x :: xs)) 
                  (FSNode (MkFileInfo name md) ys) 
                    with (decEq x name)
                    
    ||| The head of the component list matches the filename stored in 
    ||| the node, so we recurse
    provePathExists (DirPath (name :: xs)) 
                    (FSNode (MkFileInfo name md) ys) 
                      | (Yes Refl) = assert_total $ do
      ((path, fs) ** prf) <- 
        ( listToMaybe 
        . catMaybes
        . recurse (DirPath xs)
        ) ys
      case path of
        (FilePath xs x) => Nothing
        (DirPath xs') => 
          case decEq xs xs' of 
            (Yes Refl) => 
              case isElem fs ys of 
                (Yes prf_elem) => Just (ThereDir fs prf prf_elem name)
                (No contra) => Nothing 
            (No contra) => Nothing
            
    ||| The head of the component list does not correspond with the name 
    ||| stored in the node, hence the path does not exist.
    provePathExists (DirPath (x :: xs)) 
                    (FSNode (MkFileInfo name md) ys) 
                      | (No contra) = Nothing
                      
  ||| A directory path with a non-empty component list that 
  ||| ends in a node does not exist in the filesystem. 
  provePathExists (DirPath (x :: xs)) 
                  (FSLeaf y) = Nothing
  
  ||| Recursively search for proof on a list of FileSystem trees
  ||| TODO: pair Elem proof with FSElem proofs to prevent spurious 
  ||| call to isElem in recursive cases of provePathExists. 
  recurse : (p : Path) -> (lst : List FSTree) -> 
    List (Maybe (((Path, FSTree) >< uncurry FSElem)))
  recurse p [] = []
  recurse p (x :: xs) with (provePathExists p x) 
    recurse p (x :: xs) | Nothing = Nothing :: recurse p xs
    recurse p (x :: xs) | (Just y) = Just ((p, x) ** y) :: recurse p xs
