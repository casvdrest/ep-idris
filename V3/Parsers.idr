module Parsers

import Lightyear.Core
import Lightyear.Combinators
import Lightyear.Char
import Lightyear.Strings

import Environment

||| Create a path from a list of components
cPath : List String -> Maybe String -> Path
cPath lst Nothing = DirPath lst
cPath lst (Just x) = FilePath lst x

||| Parse a path component
pFPString : Parser String
pFPString = pack <$> many (alphaNum <|> space <|> oneOf " _-~#")

||| Parse a filename
pFileName : Parser String
pFileName = (++) <$> pFPString <* char '.' <*> pFPString

||| Parse a path
pPath : Parser Path
pPath = cPath <$> sepBy pFPString (char '/') <*> opt pFileName

||| Parse a list of paths
pPathList : Parser (List Path)
pPathList = sepBy pPath (char '\n')

||| Final parser
export
parsePathList : String -> Either String (List Path)
parsePathList = parse pPathList
