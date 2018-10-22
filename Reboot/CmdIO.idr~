module CmdIO

import Environment
import System
import Syntax
import Free
import GCurry

import Data.HVect

--import Text.Parser

%access public export

record ExecInfo r where 
  constructor MkCmdInfo 
  argc : Nat 
  inTypes : Vect argc Type 
  outType : Maybe Type 
  parse : String -> fromMaybe Unit outType
  exec : HVect inTypes -> IO String
  params : HVect inTypes 
  fn : Maybe (fromMaybe Void outType -> r) 
  

interface IOExec (t : Type -> Type) (r : Type) where 
  execInfo : ExecInfo r
  
readFileH : (fileHandle : File) -> IO String
readFileH h = loop ""
  where
    loop acc = do
      if !(fEOF h) then pure acc
      else do
        Right l <- fGetLine h | Left err => pure acc
        loop (acc ++ l)

execAndReadOutput : (cmd : String) -> IO String
execAndReadOutput cmd = do
  Right fh <- popen cmd Read | Left err => pure ""
  contents <- readFileH fh
  pclose fh
  pure contents

argc : Cmd r -> Nat
argc (Ls x f) = 1
argc (Cat x f) = 1
argc (Echo x f) = 1
argc (Return) = 0

inTypes : (cmd : Cmd r) -> Vect (argc cmd) Type
inTypes (Ls x f) = [Path]
inTypes (Cat x f) = [Path]
inTypes (Echo x f) = [String]
inTypes (Return) = []

outType : (cmd : Cmd r) -> Maybe Type 
outType (Ls x f) = Just (List Path)
outType (Cat x f) = Just String
outType (Echo x f) = Just String
outType (Return) = Nothing

getParse : (cmd : Cmd r) -> String -> fromMaybe Unit (outType cmd)
getParse (Ls x f) str = ?gp_1
getParse (Cat x f) str = ?gp_2
getParse (Echo x f) str = ?gp_3
getParse (Return) str = ()

exec : (cmd : Cmd r) -> HVect (inTypes cmd) -> IO String
exec (Ls x f) _ = execAndReadOutput ("ls " ++ show x)
exec (Cat x f) _ =  execAndReadOutput ("cat " ++ show x)
exec (Echo x f) _ =  execAndReadOutput ("echo " ++ show x)
exec Return _ =  pure ""

getParams : (cmd : Cmd r) -> HVect (inTypes cmd)
getParams (Ls x f) = [x]
getParams (Cat x f) = [x]
getParams (Echo x f) = [x]
getParams (Return) = []

getF : (cmd : Cmd r) -> Maybe (fromMaybe Unit (outType cmd) -> r)
getF (Ls x f) = Just f
getF (Cat x f) = Just f
getF (Echo x f) = Just f
getF Return = Nothing

implIO : Free Cmd r -> IO ()
implIO (Pure x) = pure ()
implIO (Bind cmd) = do 
  output_raw <- exec cmd (getParams cmd)
  fromMaybe (pure ()) 
    ( do f <- getF cmd
         let p = getParse cmd output_raw
         pure $ (implIO (f p))
    )
 
 
 
 
 
