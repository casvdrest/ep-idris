||| Contains code that enables the programmer to execute a script in the 
||| IO monad. Commands are translated to their respective shell commands, and 
||| invoked on the actual command line. Results are read back from stdout, 
||| parsed and returned. 
module CmdIO

import Environment
import System
import Syntax
import Free
import Parsers

import Data.HVect

%access public export

||| If it is a Right, return the value, otherwise
||| return the default value. 
fromRight : b -> Either a b -> b
fromRight def (Left l) = def
fromRight def (Right r) = r

||| Read command output. Taken from 
||| https://stackoverflow.com/questions/39812465/how-can-i-call-a-subprocess-in-idris 
readFileH : (fileHandle : File) -> IO String
readFileH h = loop ""
  where
    loop acc = do
      if !(fEOF h) then pure acc
      else do
        Right l <- fGetLine h | Left err => pure acc
        loop (acc ++ l)

||| Execute a command and read its output. Taken from
||| https://stackoverflow.com/questions/39812465/how-can-i-call-a-subprocess-in-idris
execAndReadOutput : (cmd : String) -> IO String
execAndReadOutput cmd = do
  Right fh <- popen cmd Read | Left err => pure ""
  contents <- readFileH fh
  pclose fh
  pure contents

||| Provides the necessary information about a datatype
||| to be able to execute it. 
interface Exec (f : Type -> Type) where 
  argc : f a -> Nat
  inTypes : (inh : f a) -> Vect (argc inh) Type 
  outType : f a -> Maybe Type 
  getParse : (inh : f a) -> String -> Either String (fromMaybe Unit (outType inh))
  exec : (inh : f a) -> HVect (inTypes inh) -> IO String
  getParams : (inh : f a) -> HVect (inTypes inh)
  getF : (inh : f a) -> Either String (fromMaybe Unit (outType inh) -> a)
               
||| Provide execution information for the Cmd type. 
implementation Exec Cmd where 
  argc (Ls x f) = 1
  argc (Cat x f) = 1
  argc (Echo x f) = 1
  argc (Return) = 0

  inTypes (Ls x f) = [Path]
  inTypes (Cat x f) = [Path]
  inTypes (Echo x f) = [String]
  inTypes (Return) = []

  outType (Ls x f) = Just (List Path)
  outType (Cat x f) = Just String
  outType (Echo x f) = Just String
  outType (Return) = Nothing

  getParse (Ls x f) str = parsePathList str
  getParse (Cat x f) str = Right str
  getParse (Echo x f) str = Right str
  getParse (Return) str = Right ()

  exec (Ls x f) _ = execAndReadOutput ("ls " ++ show x)
  exec (Cat x f) _ =  execAndReadOutput ("cat " ++ show x)
  exec (Echo x f) _ =  execAndReadOutput ("echo " ++ show x)
  exec Return _ =  pure ""

  getParams (Ls x f) = [x]
  getParams (Cat x f) = [x]
  getParams (Echo x f) = [x]
  getParams (Return) = []

  getF (Ls x f) = Right f
  getF (Cat x f) = Right f
  getF (Echo x f) = Right f
  getF Return = Left "No continuation for Return"
  
||| Describes how to execute a command in the IO monad
implIO : CmdF a -> IO ()
implIO (Pure x) = pure ()
implIO (Bind cmd) = do
  output_raw <- exec cmd (getParams cmd)
  print output_raw
  fromRight (pure ())
    ( do f <- getF cmd
         p <- getParse cmd output_raw
         pure $ (implIO (f p))
    )

||| Commands can be executed in the IO monad. 
implementation CmdExec IO where 
  cmdExec = implIO

