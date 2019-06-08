module ReplParser where

import Text.Megaparsec
import Text.Megaparsec.Char
import Control.Monad.Reader
    
import Parser
import AST

data ReplCmd 
    = EvalCmd Expr
    | LetCmd Expr Expr
    | TypeLetCmd Name Expr
    | QuitCmd
    | TypeCmd Expr
    | ListCmd
    | LoadCmd FilePath

pCmd :: Parser ctx ReplCmd
pCmd =  pQuitCmd
    <|> pTypeCmd
    <|> pListCmd
    <|> pLoadCmd
    <|> pTypeLetCmd
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
pTypeLetCmd = do
    symbol "type"
    n <- pIdent
    symbol "="
    t <- pType
    return $ TypeLetCmd (User n) t
pEvalLetCmd = do
    notFollowedBy $ char ':'
    e1 <- pExpr
    (do try $ symbol "="
        e2 <- pExpr
        return $ LetCmd e1 e2) <|> (return $ EvalCmd e1)
    
parseRepl internals = parse (runReaderT (sc *> pCmd <* eof) internals)