module File

import Control.ST
import Control.ST.ImplicitCall
import Permissions
import System
import Data.Vect

-- SO hack to capture output from stdout when
-- executing a command
readFileH : (fileHandle : File) -> IO String
readFileH h = loop ""
  where
    loop acc = do
      if !(fEOF h) then pure acc
      else do
        Right l <- fGetLine h | Left err => pure acc
        loop (acc ++ l)

-- SO hack to capture output from stdout when
-- executing a command
execAndReadOutput : (cmd : String) -> IO String
execAndReadOutput cmd = do
  Right fh <- popen cmd Read | Left err => pure ""
  contents <- readFileH fh
  pclose fh
  pure contents

interface Shell (m : Type -> Type) where
  access : FMod -> Type
  request : (file : FileInfo) -> (mod : FMod) -> ST m Var [add (access mod)]
  release : (file : Var) -> (mod : FMod) -> ST m () [remove file (access mod)]
  cat  : (file : Var) -> ST m String [file ::: access R]
  echo : ConsoleIO m => String -> ST m () []

implementation Shell IO where
  access _ = State FileInfo
  cat file = do
    MkFileInfo path _ <- read file
    captured <- lift $ execAndReadOutput $ "cat " ++ path
    pure captured
  request f _ = do
    file <- new f
    pure file
  release file _ = delete file
  echo = putStr

exampleFile : FileInfo
exampleFile = MkFileInfo "files/lorem.txt" (MkFileMD F perms user)
  where perms : FPermission
        perms = [[True,True,False],[True,True,False],[False,False,False]]
        user : User
        user = ("root", "admins")

exampleUser : User
exampleUser = ("cas", "admins")

script : (Shell m, ConsoleIO m) => ST m () []
script = do
  file <- request exampleFile R
  echo !(cat file)
  release file R
  pure ()
