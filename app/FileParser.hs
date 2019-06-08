module FileParser where

import Text.Megaparsec
import Control.Monad.Reader
    
import Parser
import AST

data FileLine = LetLine String Expr Expr
             |  TypeLine String Expr

pFileParser :: Parser ctx [FileLine]
pFileParser =
    many $ (do
        try $ symbol "type"
        n <- pIdent
        operator "="
        t <- pType
        return $ TypeLine n t) <|> (do
        n <- try pIdent
        operator ":"
        t <- pType
        operator "="
        v <- pExpr
        return $ LetLine n t v)
       
parseFile internals = parse (runReaderT (sc *> pFileParser <* eof) internals)