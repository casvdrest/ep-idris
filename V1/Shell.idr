module TSS.Shell

import Contract
import FileSystem
import Control.ST
import Control.ST.ImplicitCall

%access public export

||| Implementation of the 'cat' command
||| TODO: actually implement this
cat_impl : ST IO () []
cat_impl = do
  putStr "cat was called"

||| Implementation of the 'ls' command
||| TODO: actually implement this
ls_impl : ST IO () []
ls_impl = do
  putStr "ls was called"

-- Embedding of the "cat" command: read the contents of a file and
-- output to the command line. (This is obviously not what cat actually does,
-- but we'll pretend it does anyway)
syntax cat [file] =
  -- cat "file" is only possible if "file" exists,3512JE
  -- "file" does not refer to a directory, and
  -- the current user has read access on "file"
  {{ (exists file) /\
     (isFile file) /\
     (accessRead file)
  }}-
    id
  -{{ true }}
  ~> call cat_impl

-- Embedding of the "ls" command: read the contents of a directory and
-- write to standard output.
syntax ls [path] =
  -- A directory listing can only be done if the directory actually exists,
  -- the path refers to a directory, and the current user has read access
  -- to that directory.
  {{ exists path /\ isDirectory path {-/\ accessRead path -} }}-
    id
  -{{ true }}
  ~> call ls_impl


||| Example script. Should not compile, as the path used in the
||| 'cat' command is not known to be the same as the one in the contract.
|||
||| Should not compile!
myScript : (path : Path) -> {contract : Var}
                         -> ST IO () [
                              contract ::: Composite [
                                Require (MkCapability (FilePath ["directory"] "file.txt") R)
                              , Require (MkCapability (DirPath ["directory"]) R)
                              ]
                            ]

myScript path = do
  call (cat (FilePath ["directory"] "file.txt"))
  --call (ls (DirPath ["directory"]))
