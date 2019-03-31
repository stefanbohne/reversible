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
    _ <- try $ symbol "["
    es <- pList pExpr
    _ <- symbol "]"
    return $ foldr ECons (ELit $ VList []) es
pTupleExpr = do
    _ <- try $ symbol "("
    es <- pList pExpr
    _ <- symbol ")"
    return $ foldr foldTup (ELit VUnit) es
    where 
        foldTup l (ELit VUnit) = l
        foldTup l r = EPair l r
pList p = try(do
        a <- p
        pListNext a) <|> (return [])
    where
        pListNext a = (do
            _ <- try $ operator ","
            b <- pList p
            return $ a : b) <|> (return [a])
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
pExpr = (do
    _ <- try $ operator "\\"
    p <- pExpr
    _ <- operator "=>"
    b <- pExpr
    return $ ELam p b) <|> pExprArith

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
    _ <- try $ symbol "("
    es <- pList pType
    _ <- symbol ")"
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
