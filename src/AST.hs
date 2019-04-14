module AST where

import Prelude hiding (lookup)
import qualified Data.List
import Algebra.Lattice
import Algebra.PartialOrd
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State.Strict

import Result
import Context

data Name = User String
          | Auto String Int
          deriving (Eq)
instance Show Name where
    show (User n) = n
    show (Auto n i) = n ++ "$" ++ show i


data JanusClass = JFun | JRev
    deriving (Eq)
instance Show JanusClass where
    show JFun = "->"
    show JRev = "<=>"
instance JoinSemiLattice JanusClass where
    JFun \/ _ = JFun
    _ \/ JFun = JFun
    JRev \/ JRev = JRev
instance MeetSemiLattice JanusClass where
    JRev /\ _ = JRev
    _ /\ JRev = JRev
    JFun /\ JFun = JFun
instance Lattice JanusClass
instance PartialOrd JanusClass where 
    leq a b = leq (Join a) (Join b)
    

data Type =
        TInt | TBool | TString | TChar | TTop | TBottom
    |   TUnit
    |   TList Type
    |   TFun JanusClass Type Type
    |   TPair Type Type
    deriving (Eq)
instance Show Type where
    show TInt = "Int"
    show TBool = "Bool"
    show TString = "String"
    show TChar = "Char"
    show (TPair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (TUnit) = "()"
    show (TList a) = "[" ++ show a ++ "]"
    show TTop = "Top"
    show TBottom = "Bottom"
    show (TFun jc at rt) = "(" ++ show at ++ " " ++ show jc ++ " " ++ show rt ++ ")"
instance JoinSemiLattice Type where
    TBottom \/ r = r
    l \/ TBottom = l
    l \/ r | l == r = l
    (TFun j1 at1 rt1) \/ (TFun j2 at2 rt2) = TFun (j1 \/ j2) (at1 /\ at2) (rt1 \/ rt2)
    (TPair a1 b1) \/ (TPair a2 b2) = TPair (a1 \/ a2) (b1 \/ b2)
    (TList t1) \/ (TList t2) = TList (t1 \/ t2)
    _ \/ _ = TTop
instance MeetSemiLattice Type where
    TTop /\ r = r
    l /\ TTop = l
    l /\ r | l == r = l
    (TFun j1 at1 rt1) /\ (TFun j2 at2 rt2) = TFun (j1 /\ j2) (at1 \/ at2) (rt1 /\ rt2)
    (TPair a1 b1) /\ (TPair a2 b2) = TPair (a1 /\ a2) (b1 /\ b2)
    (TList t1) /\ (TList t2) = TList (t1 /\ t2)
    _ /\ _ = TBottom
instance PartialOrd Type where
    leq l r = leq (Join l) (Join r)
tPairFold :: [Type] -> Type
tPairFold vs = foldr f TUnit vs
    where f l TUnit = l
          f l r@(TPair _ _) = TPair l r
          f l r = TPair l r
    
typeRev:: Type -> Type
typeRev TTop = TBottom
typeRev TBottom = TTop
typeRev (TList t) = TList (typeRev t)
typeRev (TPair a b) = TPair (typeRev a) (typeRev b)
typeRev (TFun j at rt) = TFun j (typeRev at) (typeRev rt)
typeRev t = t

isEquType :: Type -> Bool
isEquType TInt = True
isEquType TBool = True
isEquType TString = True
isEquType TChar = True
isEquType TUnit = True
isEquType TBottom = True
isEquType (TList t) = isEquType t
isEquType (TPair a b) = isEquType a && isEquType b
isEquType _ = False

data Value =
        VInt Int
    |   VBool Bool
    |   VString String
    |   VChar Char
    |   VPair Value Value
    |   VUnit
    |   VList [Value]
    |   VLitFun JanusClass Type Type String (Value -> Result Value) String (Value -> Result Value)
    |   VFun Expr Expr
    |   VFix Expr [(Name, Type, Expr)]
instance Show Value where
    show (VInt i) = show i
    show (VBool b) = show b
    show (VString s) = show s
    show (VChar c) = show c
    show (VLitFun _ _ _ n _ _ _) = n
    show (VFun p b) = "(\\" ++ show p ++ " => " ++ show b ++ ")"
    show (VFix e es) = show e
    show (VPair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (VUnit) = "()"
    show (VList l) = "[" ++ (Data.List.intercalate ", " $ map show l) ++ "]"
instance Eq Value where
    (VInt i1) == (VInt i2) = i1 == i2
    (VBool b1) == (VBool b2) = b1 == b2
    (VString s1) == (VString s2) = s1 == s2
    (VChar c1) == (VChar c2) = c1 == c2
    (VLitFun _ _ _ n1 _ _ _) == (VLitFun _ _ _ n2 _ _ _) = n1 == n2
    (VFun p1 b1) == (VFun p2 b2) = p1 == p2 && b1 == b2
    (VPair a1 b1) == (VPair a2 b2) = a1 == a2 && b1 == b2
    (VUnit) == (VUnit) = True
    (VList l1) == (VList l2) = l1 == l2
    _ == _ = False
vPairFold :: [Value] -> Value
vPairFold vs = foldr f VUnit vs
    where f l VUnit = l
          f l r@(VPair _ _) = VPair l r
          f l r = VPair l r

typeOfLit :: Bool -> Value -> Type
typeOfLit _ (VInt _) = TInt
typeOfLit _ (VBool _) = TBool
typeOfLit _ (VString _) = TString
typeOfLit _ (VChar _) = TChar
typeOfLit _ (VLitFun j at rt _ _ _ _) = TFun j at rt
typeOfLit _ (VFun _ _) = error "runtime-only value"
typeOfLit fw (VPair a b) = TPair (typeOfLit fw a) (typeOfLit fw b)
typeOfLit _ (VUnit) = TUnit
typeOfLit fw (VList []) = TList (if fw then TBottom else TTop)
typeOfLit fw (VList (x : _)) = TList (typeOfLit fw x)

data Expr = 
        ELit Value
    |   EVar Name 
    |   EApp Expr Expr
    |   ELam Expr Expr
    |   ETLam Name Expr
    |   ETyped Expr Type
    |   EPair Expr Expr
    |   ECaseOf Expr [(Expr, Expr)]
    |   EDup Expr
    |   ERev Expr
    |   ECons Expr Expr
    |   EFix [(Name, Type, Expr)]
    deriving (Eq)
instance Show Expr where
    show (ELit v) = show v
    show (EVar n) = show n
    show (EDup e) = "&(" ++ show e ++ ")"
    show (EApp f a) = show f ++ "(" ++ show a ++ ")"
    show (ERev f) = show f ++ "~"
    show (ELam p b) = "\\" ++ show p ++ " -> " ++ show b
    show (ETyped e t) = "(" ++ show e ++ "): " ++ show t
    show (EPair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (ECons x r) = "(" ++ show x ++ " :: " ++ show r ++ ")"
    show (EFix es) = "fix(" ++ Data.List.intercalate ", " (map (\(n, t, e) -> show n ++ ": " ++ show t ++ " = " ++ show e) es) ++ ")"
    show (ECaseOf e [(p, v)]) = "let " ++ show p ++ " = " ++ show e ++ " in " ++ show v
    show (ECaseOf e cs) = "case " ++ show e ++ " of " ++ 
            (Data.List.intercalate " " $ map (\(p, v) -> show p ++ " => " ++ show v ++ ";") cs)
ePairFold :: [Expr] -> Expr
ePairFold vs = foldr f (ELit $ VUnit) vs
    where f l (ELit VUnit) = l
          f l r@(EPair _ _) = EPair l r
          f l r = EPair l r
            
subst :: (Alternative m, Monad m) => (Name -> m Expr) -> Expr -> m Expr
subst f e = runReaderT (subst_ e) f
subst_ :: (Alternative m, Monad m) => Expr -> ReaderT (Name -> m Expr) m Expr 
subst_ (ELit v) =
    return $ ELit v
subst_ (EVar n) = do
    s <- ask
    lift $ s n
subst_ (EApp f a) = do
    a <- subst_ a
    f <- subst_ f
    return $ EApp f a
subst_ (ELam p b) = do
    p <- subst_ p
    b <- subst_ b
    return $ ELam p b
subst_ (EDup e) = do
    e <- subst_ e
    return $ EDup e
subst_ (ERev e) = do
    e <- subst_ e
    return $ ERev e
subst_ (ETyped e t) = do
    e <- subst_ e
    return $ ETyped e t
subst_ (EPair e1 e2) = do
    e1 <- subst_ e1
    e2 <- subst_ e2
    return $ EPair e1 e2
subst_ (ECons e1 e2) = do
    e1 <- subst_ e1
    e2 <- subst_ e2
    return $ ECons e1 e2
subst_ (EFix es) = do
    es <- forM es $ \(n, t, e) -> do e <- subst_ e; return (n, t, e)
    return $ EFix es
subst_ (ECaseOf e cs) = do
    e <- subst_ e
    cs <- mapM (\(p, v) -> do
        p <- subst_ p
        v <- subst_ v
        return (p, v)) cs
    return $ ECaseOf e cs