module AST where

import Data.List
import Algebra.Lattice
import Algebra.PartialOrd

import Result

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
        TInt | TBool | TString | TChar
    |   TFun JanusClass Type Type
    |   TPair Type Type
    |   TUnit
    |   TList Type
    |   TTop
    |   TBottom
    deriving (Eq)
instance Show Type where
    show TInt = "Int"
    show TBool = "Bool"
    show TString = "String"
    show (TFun jc at rt) = "(" ++ show at ++ " " ++ show jc ++ " " ++ show rt ++ ")"
    show (TPair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (TUnit) = "()"
    show (TList a) = "[" ++ show a ++ "]"
    show (TTop) = "Top"
    show (TBottom) = "Bottom"
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

type EvalContext = [(String, Value)]

data Value =
        VInt Int
    |   VBool Bool
    |   VString String
    |   VChar Char
    |   VLitFun JanusClass Type Type String (Value -> Result Value) String (Value -> Result Value)
    |   VFun EvalContext Expr Expr
    |   VPair Value Value
    |   VUnit
    |   VList [Value]
instance Show Value where
    show (VInt i) = show i
    show (VBool b) = show b
    show (VString s) = show s
    show (VChar c) = show c
    show (VFun _ p b) = "fun " ++ show p ++ " -> " ++ show b
    show (VLitFun _ _ _ n _ _ _) = "(" ++ n ++ ")"
    show (VPair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (VUnit) = "()"
    show (VList l) = "[" ++ (intercalate ", " $ map show l) ++ "]"
instance Eq Value where
    (VInt i1) == (VInt i2) = i1 == i2
    (VBool b1) == (VBool b2) = b1 == b2
    (VString s1) == (VString s2) = s1 == s2
    (VChar c1) == (VChar c2) = c1 == c2
    (VLitFun _ _ _ n1 _ _ _) == (VLitFun _ _ _ n2 _ _ _) = n1 == n2
    (VFun _ p1 b1) == (VFun _ p2 b2) = p1 == p2 && b1 == b2
    (VPair a1 b1) == (VPair a2 b2) = a1 == a2 && b1 == b2
    (VUnit) == (VUnit) = True
    (VList l1) == (VList l2) = l1 == l2

typeOfLit :: Bool -> Value -> Type
typeOfLit _ (VInt _) = TInt
typeOfLit _ (VBool _) = TBool
typeOfLit _ (VString _) = TString
typeOfLit _ (VChar _) = TChar
typeOfLit _ (VLitFun j at rt _ _ _ _) = TFun j at rt
typeOfLit _ (VFun _ _ _) = error "runtime-only value"
typeOfLit fw (VPair a b) = TPair (typeOfLit fw a) (typeOfLit fw b)
typeOfLit _ (VUnit) = TUnit
typeOfLit fw (VList []) = TList (if fw then TBottom else TTop)
typeOfLit fw (VList (x : _)) = TList (typeOfLit fw x)

data Expr = 
        ELit Value
    |   EVar String 
    |   EDup Expr
    |   EApp Expr Expr
    |   ERev Expr
    |   ELam Expr Expr
    |   ELet Expr Expr Expr
    |   ETyped Expr Type
    |   EPair Expr Expr
    |   ECons Expr Expr
    deriving (Eq)
instance Show Expr where
    show (ELit v) = show v
    show (EVar n) = n
    show (EDup e) = "&(" ++ show e ++ ")"
    show (EApp f a) = show f ++ "(" ++ show a ++ ")"
    show (ERev f) = show f ++ "~"
    show (ELam p b) = "\\" ++ show p ++ " -> " ++ show b
    show (ELet p v s) = "let " ++ show p ++ " = " ++ show v ++ "; " ++ show s
    show (ETyped e t) = "(" ++ show e ++ "): " ++ show t
    show (EPair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (ECons x r) = "(" ++ show x ++ " :: " ++ show r ++ ")"

    
checkInt (VInt i) = Success i
checkInt v = Rejected $ (show v) ++ " is not an Int"

checkBool (VBool b) = Success b
checkBool v = Rejected $ (show v) ++ " is not a Bool"

checkString (VString s) = Success s
checkString v = Rejected $ (show v) ++ " is not a String"

checkChar (VChar c) = Success c
checkChar v = Rejected $ (show v) ++ " is not a Char"

checkList (VList l) = Success l
checkList v = Rejected $ (show v) ++ " is not a list"

checkPair (VPair a b) = Success (a, b)
checkPair v = Rejected $ (show v) ++ " is not a tuple"

checkCons (VList (a : b)) = Success (a, b)
checkCons v@(VList []) = TypeError $ (show v) ++ " is not a non-empty list"
checkCons v = Rejected $ (show v) ++ " is not a list"

reverseFun :: Value -> Result Value
reverseFun (VFun ctx p b) = Success $ VFun ctx b p
reverseFun (VLitFun jc t1 t2 n1 f1 n2 f2) = Success $ VLitFun jc t2 t1 n2 f2 n1 f1
reverseFun v = Rejected $ (show v) ++ " is not a function"


opPlus :: Value
opPlus = VLitFun JFun TInt (TFun JRev TInt TInt) "+" (\r -> do
    r <- typeRequired $ checkInt r
    return $ opPlusK r) "" (\_ -> TypeError $ "not reversible")
opMinus :: Value
opMinus = VLitFun JFun TInt (TFun JRev TInt TInt) "-" (\r -> do
    r <- typeRequired $ checkInt r
    typeRequired $ reverseFun $ opPlusK r) "" (\_ -> TypeError $ "not reversible")
opPlusK :: Int -> Value
opPlusK r = VLitFun JRev TInt TInt ("+" ++ show r) (\l -> do
        l <- typeRequired $ checkInt l
        return $ VInt $ l + r) 
    ("-" ++ show r) (\l -> do
        l <- typeRequired $ checkInt l
        return $VInt $ l - r)
opMul :: Value
opMul = VLitFun JFun TInt (TFun JRev TInt TInt) "*" (\r -> do
    r <- typeRequired $ checkInt r
    return $ opMulK r) "" (\_ -> TypeError $ "not reversible")
opDiv :: Value
opDiv = VLitFun JFun TInt (TFun JRev TInt TInt) "/" (\r -> do
    r <- typeRequired $ checkInt r
    reverseFun $ opMulK r) "" (\_ -> TypeError $ "not reversible")
opMulK :: Int -> Value
opMulK r = VLitFun JRev TInt TInt ("*" ++ show r) (\l -> do
        l <- typeRequired $ checkInt l
        return $ VInt $ l * r) 
    ("/" ++ show r) (\l -> do
        l <- typeRequired $ checkInt l
        return $VInt $ l `div` r)

opConcat :: Value
opConcat = VLitFun JFun TString (TFun JFun TString TString) "++" (\r -> do
    r <- typeRequired $ checkString r
    return $ opConcatK r) "" (\_ -> TypeError $ "not reversible")
opConcatK :: String -> Value
opConcatK r = VLitFun JFun TString TString (show r ++ "++") (\l -> do
    l <- typeRequired $ checkString l
    return $ VString $ l ++ r) "" (\_ -> TypeError $ "not reversible")
opSplitAt :: Value
opSplitAt = VLitFun JFun TInt (TFun JRev TString (TPair TString TString)) "splitAt" (\n -> do
    n <- typeRequired $ checkInt n
    return $ opSplitAtK n) "" (\_ -> TypeError $ "not reversible")
opSplitAtK :: Int -> Value
opSplitAtK n = VLitFun JRev TString (TPair TString TString) ("splitAt(" ++ show n ++ ")") (\s -> do
    s <- typeRequired $ checkString s
    let (s1, s2) = splitAt n s
    return $ VPair (VString s1) (VString s2)) ("unsplitAt(" ++ show n ++ ")") (\v -> do
    (s1, s2) <- typeRequired $ checkPair v
    s1 <- typeRequired $ checkString s1
    s2 <- typeRequired $ checkString s2
    return $ VString $ s1 ++ s2)

prelude :: [(String, Value)]
prelude = [("True", VBool True),
           ("False", VBool False),
           ("splitAt", opSplitAt)]
preludeTypes = [(n, typeOfLit True v) | (n, v) <- prelude]