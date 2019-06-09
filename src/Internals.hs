module Internals where

import AST
import Result
import Eval
import Context


opPlus :: Value
opPlus = VLitFun (TFun JFun TInt (TFun JRev TInt TInt)) "+" (\r -> do
    r <- typeRequired $ checkInt r
    return $ opPlusK r) "" (\_ -> TypeError $ "not reversible")
opMinus :: Value
opMinus = VLitFun (TFun JFun TInt (TFun JRev TInt TInt)) "-" (\r -> do
    r <- typeRequired $ checkInt r
    typeRequired $ reverseFun $ opPlusK r) "" (\_ -> TypeError $ "not reversible")
opPlusK :: Int -> Value
opPlusK r = VLitFun (TFun JRev TInt TInt) ("+" ++ show r) (\l -> do
        l <- typeRequired $ checkInt l
        return $ VInt $ l + r) 
    ("-" ++ show r) (\l -> do
        l <- typeRequired $ checkInt l
        return $VInt $ l - r)
opMul :: Value
opMul = VLitFun (TFun JFun TInt (TFun JRev TInt TInt)) "*" (\r -> do
    r <- typeRequired $ checkInt r
    return $ opMulK r) "" (\_ -> TypeError $ "not reversible")
opDiv :: Value
opDiv = VLitFun (TFun JFun TInt (TFun JRev TInt TInt)) "/" (\r -> do
    r <- typeRequired $ checkInt r
    reverseFun $ opMulK r) "" (\_ -> TypeError $ "not reversible")
opMulK :: Int -> Value
opMulK r = VLitFun (TFun JRev TInt TInt) ("*" ++ show r) (\l -> do
        l <- typeRequired $ checkInt l
        return $ VInt $ l * r) 
    ("/" ++ show r) (\l -> do
        l <- typeRequired $ checkInt l
        return $VInt $ l `div` r)

opConcat :: Value
opConcat = VLitFun (TFun JFun TString (TFun JFun TString TString)) "++" (\r -> do
    r <- typeRequired $ checkString r
    return $ opConcatK r) "" (\_ -> TypeError $ "not reversible")
opConcatK :: String -> Value
opConcatK r = VLitFun (TFun JFun TString TString) (show r ++ "++") (\l -> do
    l <- typeRequired $ checkString l
    return $ VString $ l ++ r) "" (\_ -> TypeError $ "not reversible")
opSplitAt :: Value
opSplitAt = VLitFun (TFun JFun TInt (TFun JRev TString (TPair TString TString))) "splitAt" (\n -> do
    n <- typeRequired $ checkInt n
    return $ opSplitAtK n) "" (\_ -> TypeError $ "not reversible")
opSplitAtK :: Int -> Value
opSplitAtK n = VLitFun (TFun JRev TString (TPair TString TString)) ("splitAt(" ++ show n ++ ")") (\s -> do
    s <- typeRequired $ checkString s
    let (s1, s2) = splitAt n s
    return $ VPair (VString s1) (VString s2)) ("splitAt(" ++ show n ++ ")~") (\v -> do
    (s1, s2) <- typeRequired $ checkPair v
    s1 <- typeRequired $ checkString s1
    s2 <- typeRequired $ checkString s2
    return $ VString $ s1 ++ s2)

opForget :: Value
opForget = VLitFun (TForall (User "A") (TFun JFun (TVar $ User "A") (TFun JRev (TVar $ User "A") TUnit))) "forget" (
    \v -> return $ opForgetK v) "" (\_ -> TypeError $ "not reversible")
opRemember :: Value
opRemember = VLitFun (TForall (User "A") (TFun JFun (TVar $ User "A") (TFun JRev TUnit (TVar $ User "A")))) "remember" (
    \v -> reverseFun $ opForgetK v) "" (\_ -> TypeError $ "not reversible")
opForgetK :: Value -> Value
opForgetK v = VLitFun (TFun JRev TTop TUnit) ("forget(" ++ show v ++ ")") (
    \_ -> return VUnit) ("remember(" ++ show v ++ ")") (\_ -> return v)

opError :: Value
opError = VLitFun (TForall (User "A") (TFun JFun TString (TFun JRev TUnit (TVar $ User "A")))) "error" (
    \v -> do
        msg <- typeRequired $ checkString v
        return $ opErrorK msg) "" (\_ -> TypeError $ "not reversible")
opErrorK :: String -> Value
opErrorK msg = VLitFun (TFun JRev TTop TBottom) name impl name impl
    where name = "error(" ++ show msg ++ ")"
          impl v = Error msg
opReject :: Value
opReject = VLitFun (TForall (User "A") (TFun JFun TString (TFun JRev TUnit (TVar $ User "A")))) "reject" (
    \v -> do
        msg <- typeRequired $ checkString v
        return $ opRejectK msg) "" (\_ -> TypeError $ "not reversible")
opRejectK :: String -> Value
opRejectK msg = VLitFun (TFun JRev TTop TBottom) name impl name impl
    where name = "reject(" ++ show msg ++ ")"
          impl v = Rejected msg
                

_internals = [
    VBool True, 
    VBool False, 
    opSplitAt,
    opForget,
    opRemember,
    opError,
    opReject
    ]
internals :: (Context c, Monoid (c Name Value)) => c Name Value
internals = mkContext $ map (\v -> (User $ show v, v)) _internals
