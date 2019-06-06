module ReplParser where

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr 
import Control.Monad.Reader
import Data.Text (Text)
    
import Parser
import AST

data ReplCmd 
    = EvalCmd Expr
    | LetCmd Expr Expr
    | QuitCmd
    | TypeCmd Expr
    | ListCmd
    | LoadCmd FilePath

pCmd :: Parser ctx ReplCmd
pCmd =  pQuitCmd
    <|> pTypeCmd
    <|> pListCmd
    <|> pLoadCmd
    <|> pEvalLetCmd
pQuitCmd = QuitCmd <$ (symbol ":quit" <|> symbol ":q")
pTypeCmd = do
    symbol ":type" <|> symbol ":t"
    e <- pExpr
    return $ TypeCmd e
pListCmd = ListCmd <$ symbol ":list"
pLoadCmd = do
    symbol ":load" <|> symbol ":l"
    fn <- many anySingle
    return $ LoadCmd fn
pEvalLetCmd = do
    notFollowedBy $ char ':'
    e1 <- pExpr
    (do try $ symbol "="
        e2 <- pExpr
        return $ LetCmd e1 e2) <|> (return $ EvalCmd e1)
    
parseRepl internals = parse (runReaderT (sc *> pCmd <* eof) internals)