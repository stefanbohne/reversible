module ReplParser where

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr 
import Data.Text (Text)
    
import Parser
import AST

data ReplCmd 
    = EvalCmd Expr
    | LetCmd Expr Expr
    | QuitCmd
    | TypeCmd Expr
    | ListCmd

pCmd :: Parser ReplCmd
pCmd =  pQuitCmd
    <|> pTypeCmd
    <|> pListCmd
    <|> pEvalLetCmd
pQuitCmd = QuitCmd <$ (symbol ":quit" <|> symbol ":q")
pTypeCmd = do
    _ <- symbol ":type" <|> symbol ":t"
    e <- pExpr
    return $ TypeCmd e
pListCmd = ListCmd <$ (symbol ":list" <|> symbol ":l")
pEvalLetCmd = do
    _ <- notFollowedBy $ char ':'
    e1 <- pExpr
    (do _ <- try $ symbol "="
        e2 <- pExpr
        return $ LetCmd e1 e2) <|> (return $ EvalCmd e1)
    
parseRepl = parse (sc *> pCmd <* eof)