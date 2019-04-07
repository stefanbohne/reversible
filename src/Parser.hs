module Parser where

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr 
import Data.Text (Text)
import Data.Void
import Data.Proxy

import Result
import AST
import Internals

type Parser = Parsec Void Text


sc :: Parser ()
sc = L.space
  space1                         
  (L.skipLineComment "//")       
  (L.skipBlockComment "/*" "*/") 

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc 

symbol :: Text -> Parser Text
symbol = L.symbol sc 

operator :: Text -> Parser ()
operator text = do
    _ <- string text
    _ <- notFollowedBy $ oneOf ("!@#$%^&*-+=<>|/\\~:;" :: String)
    _ <- sc
    return ()
    

pIdent :: Parser String 
pIdent = do 
    h <- letterChar
    t <- many (alphaNumChar <|> char '_')
    _ <- sc
    return (h : t)

pInt :: Parser Int
pInt = L.signed sc $ lexeme L.decimal

pString :: Parser String
pString = lexeme $ char '"' >> manyTill L.charLiteral (char '"')

pChar :: Parser Char
pChar = lexeme $ char '\'' >> L.charLiteral <* (char '\'')


pExprTerm :: Parser Expr
pExprTerm = 
        EVar <$> pIdent
    <|> (ELit . VInt) <$> pInt
    <|> (ELit . VString) <$> pString
    <|> (ELit . VChar) <$> pChar
    <|> pListExpr
    <|> pTupleExpr
pListExpr = do
    es <- pList (symbol "[") pExpr (symbol "]")
    return $ foldr ECons (ELit $ VList []) es
pTupleExpr = do
    es <- pList (symbol "(") pExpr (symbol ")")
    return $ foldr foldTup (ELit VUnit) es
    where 
        foldTup l (ELit VUnit) = l
        foldTup l r = EPair l r
pList :: Parser a -> Parser b -> Parser c -> Parser [b]
pList start p end = do
    try start
    ([] <$ try end) <|> (do
        a <- p
        r <- pListNext p end
        return $ a : r)
pList1 start p end = do
        try start
        a <- p
        r <- pListNext p end
        return $ a : r
pListNext :: Parser b -> Parser c -> Parser [b]
pListNext p end = ([] <$ try end) <|> (do
    try $ operator ","
    b <- p
    r <- pListNext p end
    return $ b : r)
pExprDup = (do
    _ <- try $ operator "&"
    e <- pExprTerm
    return $ EDup e) <|> pExprTerm
pExprApp = do
    f <- pExprDup
    as <- many (((flip EApp) <$> pTupleExpr) <|>
                (ERev <$ symbol "~"))
    return $ foldl (flip ($)) f as
pExprTyped = do
    l <- pExprApp
    (do
        _ <- try $ operator ":"
        r <- pType
        return $ ETyped l r) <|> return l
pExprArith = makeExprParser pExprTyped [
        [binOpLit InfixL "*" opMul,
         binOpLit InfixL "/" opDiv],
        [binOpLit InfixL "+" opPlus,
         binOpLit InfixL "-" opMinus],
        [binOp InfixR "::" (\l r -> ECons l r),
         binOpLit InfixL "++" opConcat]
    ]
pExprLet = (do
    try $ symbol "let"
    lets <- sepBy1 (do
        p <- pExpr
        operator "="
        e <- pExpr
        return (p, e)) (try $ operator ";")
    symbol "in"
    v <- pExpr
    return $ foldr (\(p, e) v -> ECaseOf e [(p, v)]) v lets) <|> pExprArith
pExprCase = (do
    _ <- try $ symbol "case"
    e <- pExpr
    _ <- symbol "of"
    cases <- sepBy (do
        p <- pExprLet
        _ <- symbol "=>"
        v <- pExpr
        return (p, v)) (operator ";")
    _ <- optional $ try $ operator ";"
    return $ ECaseOf e cases) <|> pExprLet
pExpr = (do
    f <- try $ (((\p b -> EFix (ELam p b)) <$ (operator "\\\\")) <|> (ELam <$ (operator "\\")))
    p <- pExpr
    _ <- operator "=>"
    b <- pExpr
    return $ f p b) <|> pExprCase

pType :: Parser Type
pType = makeExprParser pSimpleType [
        [binOp InfixN "<=>" (TFun JRev)],
        [binOp InfixR "->" (TFun JFun)]
    ]
pSimpleType :: Parser Type
pSimpleType =
        TInt <$ lexeme "Int"
    <|> TBool <$ lexeme "Bool"
    <|> TString <$ lexeme "String"
    <|> TChar <$ lexeme "Char"
    <|> TTop <$ lexeme "Top"
    <|> TBottom <$ lexeme "Bottom"
    <|> pTupleType
    <|> (symbol "[") *> (TList <$> pType) <* (symbol "]")
pTupleType = do
    es <- pList (symbol "(") pType (symbol ")")
    return $ foldr foldTup (TUnit) es
    where 
        foldTup l TUnit = l
        foldTup l r = TPair l r
binOp :: (Parser (a -> a -> a) -> Operator Parser a) -> Text -> (a -> a -> a) -> Operator Parser a
binOp cons op f = cons $ do
    _ <- try $ operator op
    return f
binOpLit cons op fun = binOp cons op (\l r -> EApp (EApp (ELit fun) r) l)

parseExpr = parse (sc *> pExpr <* eof)
parseType = parse (sc *> pType <* eof)
