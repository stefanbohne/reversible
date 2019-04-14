module Internals where

import AST
import Result
import Eval
import Context

checkInt (VInt i) = Success i
checkInt v = Rejected $ (show v) ++ " is not an Int"

checkBool (VBool b) = Success b
checkBool v = Rejected $ (show v) ++ " is not a Bool"

checkString (VString s) = Success s
checkString v = Rejected $ (show v) ++ " is not a String"

checkChar (VChar c) = Success c
checkChar v = Rejected $ (show v) ++ " is not a Char"


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
    return $ VPair (VString s1) (VString s2)) ("splitAt(" ++ show n ++ ")~") (\v -> do
    (s1, s2) <- typeRequired $ checkPair v
    s1 <- typeRequired $ checkString s1
    s2 <- typeRequired $ checkString s2
    return $ VString $ s1 ++ s2)

_internals = [
    VBool True, 
    VBool False, 
    opSplitAt
    ]
internals :: (Context c, Monoid (c Name Value)) => c Name Value
internals = mkContext $ map (\v -> (User $ show v, v)) _internals
