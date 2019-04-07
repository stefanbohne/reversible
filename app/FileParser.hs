module FileParser where

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr 
import Control.Monad.Reader
import Data.Text (Text)
    
import Parser
import AST

pFileParser :: Parser ctx [(String, Type, Expr)]
pFileParser =
    many $ do
        n <- try pIdent
        operator ":"
        t <- pType
        operator "="
        v <- pExpr
        return (n, t, v)
       
parseFile internals = parse (runReaderT (sc *> pFileParser <* eof) internals)