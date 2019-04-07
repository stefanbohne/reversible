module Parser where

import Prelude hiding (lookup)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr 
import Control.Monad.Reader
import Data.Text (Text)
import Data.Void
import Data.Proxy

import Result
import AST
import Internals
import Context

type Parser c = ReaderT (c String Value) (Parsec String Text)

instance ShowErrorComponent String where
    showErrorComponent err = err

sc :: Parser c ()
sc = L.space
  space1                         
  (L.skipLineComment "//")       
  (L.skipBlockComment "/*" "*/") 

lexeme :: Parser c a -> Parser c a
lexeme = L.lexeme sc 

symbol :: Text -> Parser c Text
symbol = L.symbol sc 

operator :: Text -> Parser c ()
operator text = do
    _ <- string text
    _ <- notFollowedBy $ oneOf ("!@#$%^&*-+=<>|/\\~:;" :: String)
    _ <- sc
    return ()

binOp :: (Parser ctx (a -> a -> a) -> Operator (Parser ctx) a) -> Text -> (a -> a -> a) -> Operator (Parser ctx) a
binOp cons op f = cons $ do
    _ <- try $ operator op
    return f
binOpLit cons op fun = binOp cons op (\l r -> EApp (EApp (ELit fun) r) l)
        

pIdent :: Parser c String 
pIdent = do 
    h <- letterChar
    t <- many (alphaNumChar <|> char '_')
    _ <- sc
    return (h : t)

pInt :: Parser c Int
pInt = L.signed sc $ lexeme L.decimal

pString :: Parser c String
pString = lexeme $ char '"' >> manyTill L.charLiteral (char '"')

pChar :: Parser c Char
pChar = lexeme $ char '\'' >> L.charLiteral <* (char '\'')


pExprTerm :: Parser c Expr
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
pList :: Parser ctx a -> Parser ctx b -> Parser ctx c -> Parser ctx [b]
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
pListNext :: Parser ctx b -> Parser ctx c -> Parser ctx [b]
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

pType :: Parser ctx Type
pType = makeExprParser pSimpleType [
        [binOp InfixN "<=>" (TFun JRev)],
        [binOp InfixR "->" (TFun JFun)]
    ]
pSimpleType :: Parser ctx Type
pSimpleType =
        TInt <$ symbol "Int"
    <|> TBool <$ symbol "Bool"
    <|> TString <$ symbol "String"
    <|> TChar <$ symbol "Char"
    <|> TTop <$ symbol "Top"
    <|> TBottom <$ symbol "Bottom"
    <|> pTupleType
    <|> (symbol "[") *> (TList <$> pType) <* (symbol "]")
pTupleType :: Parser ctx Type
pTupleType = do
    es <- pList (symbol "(") pType (symbol ")")
    return $ foldr foldTup (TUnit) es
    where 
        foldTup l TUnit = l
        foldTup l r = TPair l r


parseExpr internals = parse (runReaderT (sc *> pExpr <* eof) internals)
parseType internals = parse (runReaderT (sc *> pType <* eof) internals)
