module Parser where

import Prelude hiding (lookup)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr 
import Control.Monad.Reader
import Data.Text (Text)

import AST
import Internals

type Parser c = ReaderT (c Name Value) (Parsec String Text)

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
    string text
    notFollowedBy $ oneOf ("!@#$%^&*-+=<>|/\\~:;" :: String)
    sc
    return ()

binOp :: (Parser ctx (a -> a -> a) -> Operator (Parser ctx) a) -> Text -> (a -> a -> a) -> Operator (Parser ctx) a
binOp cons op f = cons $ do
    try $ operator op
    return f
binOpLit cons op fun = binOp cons op (\l r -> EApp (EApp (ELit fun) r) l)
        

pIdent :: Parser c String 
pIdent = do 
    h <- letterChar
    t <- many (alphaNumChar <|> char '_')
    sc
    return (h : t)

pInt :: Parser c Int
pInt = L.signed sc $ lexeme L.decimal

pString :: Parser c String
pString = lexeme $ char '"' >> manyTill L.charLiteral (char '"')

pChar :: Parser c Char
pChar = lexeme $ char '\'' >> L.charLiteral <* (char '\'')


pExprTerm :: Parser c Expr
pExprTerm = 
        pExprFix
    <|> EVar <$> User <$> pIdent
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
    return $ ePairFold es
pExprFix = do
    try $ operator "fix"
    es <- pList (symbol "(") (do
        n <- User <$> try pIdent
        operator ":"
        t <- pType
        operator "="
        e <- pExpr
        return (n, t, e)) (symbol ")")
    return $ EFix es
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
    try $ operator "&"
    e <- pExprTerm
    return $ EDup e) <|> pExprTerm
pExprApp = do
    f <- pExprDup
    as <- many (((flip EApp) <$> pTupleExpr) <|>
                ((flip ETypeApp) <$> ((symbol "{") *> pType <* (symbol "}"))) <|>
                (ERev <$ symbol "~"))
    return $ foldl (flip ($)) f as
pExprTyped = do
    l <- pExprApp
    (do
        try $ operator ":"
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
    return $ foldr (\(p, e) v -> ECaseOf e [(p, v)]) v lets) <|> (do
    try $ symbol "type"
    lets <- sepBy1 (do
        n <- pIdent
        operator "="
        t <- pType
        return (User n, t)) (try $ operator ";")
    symbol "in"
    v <- pExpr
    return $ foldr (\(n, t) v -> ETypeLet n t v) v lets) <|> pExprArith
pExprCase = (do
    try $ symbol "case"
    e <- pExpr
    symbol "of"
    cases <- sepBy (do
        p <- try pExprLet
        symbol "=>"
        v <- pExpr
        return (p, v)) (operator ";")
    optional $ try $ operator ";"
    return $ ECaseOf e cases) <|> pExprLet
pExprLam = (do
    try $ operator "\\"
    p <- pExpr
    jc <- (Nothing <$ (try $ operator "=>")) <|>
          (Just JFun <$ (try $ operator "->")) <|>
          (Just JRev <$ (try $ operator "<=>"))
    b <- pExpr
    return $ ELam jc p b) <|> (do
    try $ symbol "forall"
    n <- pIdent
    operator "."
    b <- pExpr
    return $ ETypeLam (User n) b) <|> pExprCase
pExpr = pExprLam

pType :: Parser ctx Expr
pType = pForallType
pForallType = (do
    try $ symbol "forall"
    n <- pIdent
    operator "."
    t <- pType
    return $ EForallType (User n) t) <|> pFunType
pFunType = makeExprParser pTypeApp [
        [binOp InfixN "<=>" (EFunType JRev)],
        [binOp InfixR "->" (EFunType JFun)]
    ]
pTypeApp = do
    f <- pSimpleType
    as <- many ((flip EAppType) <$> ((symbol "{") *> pType <* (symbol "}")))
    return $ foldl (flip ($)) f as
pSimpleType :: Parser ctx Expr
pSimpleType =
        (ELit $ VType TInt) <$ symbol "Int"
    <|> (ELit $ VType TBool) <$ symbol "Bool"
    <|> (ELit $ VType TString) <$ symbol "String"
    <|> (ELit $ VType TChar) <$ symbol "Char"
    <|> (ELit $ VType TTop) <$ symbol "Top"
    <|> (ELit $ VType TBottom) <$ symbol "Bottom"
    <|> pTupleType
    <|> (symbol "[") *> (EListType <$> pType) <* (symbol "]")
    <|> ((EVar . User) <$> pIdent)
pTupleType :: Parser ctx Expr
pTupleType = do
    es <- pList (symbol "(") pType (symbol ")")
    return $ ePairTypeFold es


parseExpr internals = parse (runReaderT (sc *> pExpr <* eof) internals)
parseType internals = parse (runReaderT (sc *> pType <* eof) internals)
