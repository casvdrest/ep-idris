module CmdIO

import Environment
import System
import Syntax
import Free
import GCurry
import Parsers

import Data.HVect

%access public export

fromRight : b -> Either a b -> b
fromRight def (Left l) = def
fromRight def (Right r) = r

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
  
interface IOExec (f : Type -> Type) where 
  argc : f a -> Nat
  inTypes : (inh : f a) -> Vect (argc inh) Type 
  outType : f a -> Maybe Type 
  getParse : (inh : f a) -> String -> Either String (fromMaybe Unit (outType inh))
  exec : (inh : f a) -> HVect (inTypes inh) -> IO String
  getParams : (inh : f a) -> HVect (inTypes inh)
  getF : (inh : f a) -> Either String (fromMaybe Unit (outType inh) -> a)
               
implementation IOExec Cmd where 
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
  
implIO : CmdF a  -> IO ()
implIO (Pure x) = pure ()
implIO (Bind cmd) = do
  output_raw <- exec cmd (getParams cmd)
  print output_raw
  fromRight (pure ())
    ( do f <- getF cmd
         p <- getParse cmd output_raw
         pure $ (implIO (f p))
    )
    
implementation CmdExec IO where 
  cmdExec = implIO

