module AST where

import Prelude hiding (lookup)
import qualified Data.List
import Data.Functor.Identity
import Data.Maybe
import Algebra.Lattice
import Algebra.PartialOrd
import Control.Monad.Reader

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

class Substitutable a where
    subst_ :: (Monad m) => a -> ReaderT (Name -> Maybe (m a)) m a
    

data Type =
        TInt | TBool | TString | TChar | TTop | TBottom | TType
    |   TUnit
    |   TList Type
    |   TFun JanusClass Type Type
    |   TPair Type Type
    |   TForall Name Type
    |   TTypeApp Type Type
    |   TVar Name
instance Eq Type where 
    TInt == TInt = True
    TBool == TBool = True
    TString == TString = True
    TChar == TChar = True
    TTop == TTop = True
    TBottom == TBottom = True
    TType == TType = True
    TUnit == TUnit = True
    (TPair a1 b1) == (TPair a2 b2) = a1 == a2 && b1 == b2
    (TList t1) == (TList t2) = t1 == t2
    (TFun jc1 at1 rt1) == (TFun jc2 at2 rt2) = jc1 == jc2 && at1 == at2 && rt1 == rt2
    (TVar n1) == (TVar n2) = n1 == n2
    (TForall n1 t1) == (TForall n2 t2) = t1 == (runIdentity $ subst1 (n2, return $ TVar n1) t2)
    (TTypeApp f1 a1) == (TTypeApp f2 a2) = f1 == f2 && a1 == a2
    _ == _ = False
instance Show Type where
    show TInt = "Int"
    show TBool = "Bool"
    show TString = "String"
    show TChar = "Char"
    show TType = "Type"
    show (TPair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (TUnit) = "()"
    show (TList a) = "[" ++ show a ++ "]"
    show TTop = "Top"
    show TBottom = "Bottom"
    show (TFun jc at rt) = "(" ++ show at ++ " " ++ show jc ++ " " ++ show rt ++ ")"
    show (TForall n t) = "forall " ++ show n ++ ". " ++ show t
    show (TTypeApp f a) = show f ++ "{" ++ show a ++ "}"
    show (TVar n) = show n
instance Substitutable Type where
    subst_ (TVar n) = do
        s <- ask
        lift $ fromMaybe (return $ TVar n) (s n)
    subst_ (TPair a b) = do
        a <- subst_ a
        b <- subst_ b
        return $ TPair a b
    subst_ (TList a) = do
        a <- subst_ a
        return $ TList a
    subst_ (TFun jc at rt) = do
        at <- subst_ at
        rt <- subst_ rt
        return $ TFun jc at rt
    subst_ (TForall n t) = do
        t <- subst_ t
        return $ TForall n t
    subst_ (TTypeApp f a) = do
        f <- subst_ f
        a <- subst_ a
        return $ TTypeApp f a
    subst_ t =
        return t
instance JoinSemiLattice Type where
    TBottom \/ r = r
    l \/ TBottom = l
    l \/ r | l == r = l
    (TFun j1 at1 rt1) \/ (TFun j2 at2 rt2) = TFun (j1 \/ j2) (at1 /\ at2) (rt1 \/ rt2)
    (TPair a1 b1) \/ (TPair a2 b2) = TPair (a1 \/ a2) (b1 \/ b2)
    (TList t1) \/ (TList t2) = TList (t1 \/ t2)
    (TForall n1 t1) \/ (TForall n2 t2) = 
        let t2subst = runIdentity $ subst1 (n2, return (TVar n1)) t2 in
        TForall n1 (t1 \/ t2subst)
    (TTypeApp f1 a1) \/ (TTypeApp f2 a2) =
        TTypeApp (f1 \/ f2) (a1 \/ a2)
    _ \/ _ = TTop
instance MeetSemiLattice Type where
    TTop /\ r = r
    l /\ TTop = l
    l /\ r | l == r = l
    (TFun j1 at1 rt1) /\ (TFun j2 at2 rt2) = TFun (j1 /\ j2) (at1 \/ at2) (rt1 /\ rt2)
    (TPair a1 b1) /\ (TPair a2 b2) = TPair (a1 /\ a2) (b1 /\ b2)
    (TList t1) /\ (TList t2) = TList (t1 /\ t2)
    (TForall n1 t1) /\ (TForall n2 t2) = 
        let t2subst = runIdentity $ subst1 (n2, return $ TVar n1) t2 in
        TForall n1 (t1 /\ t2subst)
    (TTypeApp f1 a1) /\ (TTypeApp f2 a2) =
        TTypeApp (f1 /\ f2) (a1 /\ a2)
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
typeRev (TForall n t) = TForall n (typeRev t) 
typeRev (TTypeApp f a) = TTypeApp (typeRev f) (typeRev a)
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
    |   VLitFun Type String (Value -> Result Value) String (Value -> Result Value)
    |   VFun (IndexList Name Value) Expr Expr
    |   VFix Expr [(Name, Expr)]
    |   VType Type
instance Show Value where
    show (VInt i) = show i
    show (VBool b) = show b
    show (VString s) = show s
    show (VChar c) = show c
    show (VLitFun _ n _ _ _) = n
    show (VFun env p b) = "#(\\" ++ show p ++ " => " ++ show b ++ ")#" ++ showContext env
    show (VFix e es) = "#fixed(" ++ show e ++ ")"
    show (VPair a b) = "#(" ++ show a ++ ", " ++ show b ++ ")"
    show (VUnit) = "()"
    show (VList l) = "#[" ++ (Data.List.intercalate ", " $ map show l) ++ "]"
    show (VType t) = show t
instance Eq Value where
    (VInt i1) == (VInt i2) = i1 == i2
    (VBool b1) == (VBool b2) = b1 == b2
    (VString s1) == (VString s2) = s1 == s2
    (VChar c1) == (VChar c2) = c1 == c2
    (VLitFun _ n1 _ _ _) == (VLitFun _ n2 _ _ _) = n1 == n2
    (VFun env1 p1 b1) == (VFun env2 p2 b2) = env1 == env2 && p1 == p2 && b1 == b2
    (VPair a1 b1) == (VPair a2 b2) = a1 == a2 && b1 == b2
    (VUnit) == (VUnit) = True
    (VList l1) == (VList l2) = l1 == l2
    (VType t1) == (VType t2) = t1 == t2
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
typeOfLit _ (VType _) = TType
typeOfLit _ (VLitFun t _ _ _ _) = t
typeOfLit _ (VFun _ _ _) = error "runtime-only value"
typeOfLit fw (VPair a b) = TPair (typeOfLit fw a) (typeOfLit fw b)
typeOfLit _ (VUnit) = TUnit
typeOfLit fw (VList []) = TList (if fw then TBottom else TTop)
typeOfLit fw (VList (x : _)) = TList (typeOfLit fw x)

data Expr = 
        ELit Value
    |   EVar Name 
    |   EApp Expr Expr
    |   ETypeApp Expr Expr
    |   EAppType Expr Expr
    |   ELam Expr Expr
    |   ETypeLam Name Expr
    |   EFunType JanusClass Expr Expr
    |   ETyped Expr Expr
    |   EPair Expr Expr
    |   EPairType Expr Expr
    |   ECaseOf Expr [(Expr, Expr)]
    |   EDup Expr
    |   ERev Expr
    |   ECons Expr Expr
    |   EListType Expr
    |   EFix [(Name, Expr, Expr)]
    |   EForallType Name Expr
    |   ETypeLet Name Expr Expr
    deriving (Eq)
instance Show Expr where
    show (ELit v) = show v
    show (EVar n) = show n
    show (EDup e) = "&(" ++ show e ++ ")"
    show (EApp f a) = show f ++ "(" ++ show a ++ ")"
    show (ETypeApp f a) = show f ++ "{" ++ show a ++ "}"
    show (EAppType f a) = show f ++ "{" ++ show a ++ "}"
    show (ERev f) = show f ++ "~"
    show (ELam p b) = "(\\" ++ show p ++ " => " ++ show b ++ ")"
    show (ETypeLam n b) = "forall " ++ show n ++ ". " ++ show b
    show (EFunType j at rt) = show at ++ " " ++ show j ++ " " ++ show rt
    show (ETyped e t) = "(" ++ show e ++ "): " ++ show t
    show (EPair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (EPairType a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (ECons x r) = "(" ++ show x ++ " :: " ++ show r ++ ")"
    show (EListType t) = "[" ++ show t ++ "]"
    show (EFix es) = "fix(" ++ Data.List.intercalate ", " (map (\(n, t, e) -> show n ++ ": " ++ show t ++ " = " ++ show e) es) ++ ")"
    show (ECaseOf e [(p, v)]) = "let " ++ show p ++ " = " ++ show e ++ " in " ++ show v
    show (ECaseOf e cs) = "case " ++ show e ++ " of " ++ 
            (Data.List.intercalate " " $ map (\(p, v) -> show p ++ " => " ++ show v ++ ";") cs)
    show (EForallType n t) = "forall " ++ show n ++ ". " ++ show t
    show (ETypeLet n t v) = "type " ++ show n ++ " = " ++ show t ++ " in " ++ show v
ePairFold :: [Expr] -> Expr
ePairFold vs = foldr f (ELit $ VUnit) vs
    where f l (ELit VUnit) = l
          f l r@(EPair _ _) = EPair l r
          f l r = EPair l r
ePairTypeFold :: [Expr] -> Expr
ePairTypeFold vs = foldr f (ELit (VType TUnit)) vs
    where f l (ELit (VType TUnit)) = l
          f l r@(EPairType _ _) = EPairType l r
          f l r = EPairType l r
                      
subst :: (Substitutable a, Monad m) => (Name -> Maybe (m a)) -> a -> m a
subst f e = runReaderT (subst_ e) f
subst1 :: (Substitutable a, Monad m) => (Name, m a) -> a -> m a
subst1 (n, r) e = subst (\n' -> if n' == n then Just r else Nothing) e

instance Substitutable Expr where
    subst_ (ELit v) =
        return $ ELit v
    subst_ (EVar n) = do
        s <- ask
        lift $ fromMaybe (return $ EVar n) (s n)
    subst_ (EApp f a) = do
        a <- subst_ a
        f <- subst_ f
        return $ EApp f a
    subst_ (ETypeApp f a) = do
        a <- subst_ a
        f <- subst_ f
        return $ ETypeApp f a
    subst_ (EAppType f a) = do
        a <- subst_ a
        f <- subst_ f
        return $ ETypeApp f a
    subst_ (ELam p b) = do
        p <- subst_ p
        b <- subst_ b
        return $ ELam p b
    subst_ (ETypeLam n b) = do
        b <- subst_ b
        return $ ETypeLam n b
    subst_ (EFunType j at rt) = do
        at <- subst_ at
        rt <- subst_ rt
        return $ EFunType j at rt
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
    subst_ (EPairType a b) = do
        a <- subst_ a
        b <- subst_ b
        return $ EPairType a b
    subst_ (ECons e1 e2) = do
        e1 <- subst_ e1
        e2 <- subst_ e2
        return $ ECons e1 e2
    subst_ (EListType t) = do
        t <- subst_ t
        return $ EListType t
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
    subst_ (EForallType n t) = do
        t <- subst_ t
        return $ EForallType n t
    subst_ (ETypeLet n t v) = do
        t <- subst_ t
        v <- subst_ v
        return $ ETypeLet n t v