module Parsers

import Lightyear.Core
import Lightyear.Combinators
import Lightyear.Char
import Lightyear.Strings

import Environment

cPath : List String -> Maybe String -> Path
cPath lst Nothing = DirPath lst
cPath lst (Just x) = FilePath lst x

pFPString : Parser String 
pFPString = pack <$> many (alphaNum <|> space <|> oneOf " _-~#")

pFileName : Parser String
pFileName = (++) <$> pFPString <* char '.' <*> pFPString

pPath : Parser Path
pPath = cPath <$> sepBy pFPString (char '/') <*> opt pFileName

pPathList : Parser (List Path)
pPathList = sepBy pPath (char '\n')

export
parsePathList : String -> Either String (List Path)
parsePathList = parse pPathList
 
