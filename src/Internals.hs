module Internals where

import qualified Debug.Trace

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
opEqu :: Value
opEqu = VLitFun (TFun JFun TInt (TFun JFun TInt TBool)) "==" (\r -> do
    r <- typeRequired $ checkInt r
    return $ opEquK r) "" (\_ -> TypeError $ "not reversible")
opEquK :: Int -> Value
opEquK r = VLitFun (TFun JFun TInt TBool) ("==" ++ show r) (\l -> do
    l <- typeRequired $ checkInt l
    return $ VBool $ l == r) "" (\_ -> TypeError $ "not reversible")
opNEq :: Value
opNEq = VLitFun (TFun JFun TInt (TFun JFun TInt TBool)) "!=" (\r -> do
    r <- typeRequired $ checkInt r
    return $ opNEqK r) "" (\_ -> TypeError $ "not reversible")
opNEqK :: Int -> Value
opNEqK r = VLitFun (TFun JFun TInt TBool) ("!=" ++ show r) (\l -> do
    l <- typeRequired $ checkInt l
    return $ VBool $ l /= r) "" (\_ -> TypeError $ "not reversible")
opLEq :: Value
opLEq = VLitFun (TFun JFun TInt (TFun JFun TInt TBool)) "<=" (\r -> do
    r <- typeRequired $ checkInt r
    return $ opLEqK r) "" (\_ -> TypeError $ "not reversible")
opLEqK :: Int -> Value
opLEqK r = VLitFun (TFun JFun TInt TBool) ("<=" ++ show r) (\l -> do
    l <- typeRequired $ checkInt l
    return $ VBool $ l <= r) "" (\_ -> TypeError $ "not reversible")
opLTh :: Value
opLTh = VLitFun (TFun JFun TInt (TFun JFun TInt TBool)) "<" (\r -> do
    r <- typeRequired $ checkInt r
    return $ opLThK r) "" (\_ -> TypeError $ "not reversible")
opLThK :: Int -> Value
opLThK r = VLitFun (TFun JFun TInt TBool) ("<" ++ show r) (\l -> do
    l <- typeRequired $ checkInt l
    return $ VBool $ l < r) "" (\_ -> TypeError $ "not reversible")
opGEq :: Value
opGEq = VLitFun (TFun JFun TInt (TFun JFun TInt TBool)) ">=" (\r -> do
    r <- typeRequired $ checkInt r
    return $ opGEqK r) "" (\_ -> TypeError $ "not reversible")
opGEqK :: Int -> Value
opGEqK r = VLitFun (TFun JFun TInt TBool) (">=" ++ show r) (\l -> do
    l <- typeRequired $ checkInt l
    return $ VBool $ l >= r) "" (\_ -> TypeError $ "not reversible")
opGTh :: Value
opGTh = VLitFun (TFun JFun TInt (TFun JFun TInt TBool)) ">" (\r -> do
    r <- typeRequired $ checkInt r
    return $ opGThK r) "" (\_ -> TypeError $ "not reversible")
opGThK :: Int -> Value
opGThK r = VLitFun (TFun JFun TInt TBool) (">" ++ show r) (\l -> do
    l <- typeRequired $ checkInt l
    return $ VBool $ l > r) "" (\_ -> TypeError $ "not reversible")
opAnd :: Value
opAnd = VLitFun (TFun JFun TBool (TFun JFun TBool TBool)) "&&" (\r -> do
    r <- typeRequired $ checkBool r
    return $ opAndK r) "" (\_ -> TypeError $ "not reversible")
opAndK :: Bool -> Value
opAndK r = VLitFun (TFun JFun TBool TBool) ("&&" ++ show r) (\l -> do
    l <- typeRequired $ checkBool l
    return $ VBool $ l && r) "" (\_ -> TypeError $ "not reversible")
opOr :: Value
opOr = VLitFun (TFun JFun TBool (TFun JFun TBool TBool)) "||" (\r -> do
    r <- typeRequired $ checkBool r
    return $ opOrK r) "" (\_ -> TypeError $ "not reversible")
opOrK :: Bool -> Value
opOrK r = VLitFun (TFun JFun TBool TBool) ("||" ++ show r) (\l -> do
    l <- typeRequired $ checkBool l
    return $ VBool $ l || r) "" (\_ -> TypeError $ "not reversible")
                
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
opDebug :: Value
opDebug = VLitFun (TForall (User "A") (TFun JFun TTop (TFun JRev (TVar $ User "A") (TVar $ User "A")))) "debug" (
    \v -> return $ opDebugK v) "" (\_ -> TypeError $ "not reversible")
opDebugK :: Value -> Value
opDebugK k = VLitFun (TFun JRev TTop TBottom) name impl name impl
    where name = "debug(" ++ show k ++ ")"
          impl v =
            Debug.Trace.trace (show k ++ " " ++ show v) (return v)
    

_internals = [
    VBool True, 
    VBool False, 
    opSplitAt,
    opForget,
    opRemember,
    opError,
    opReject,
    opDebug
    ]
internals :: (Context c, Monoid (c Name Value)) => c Name Value
internals = mkContext $ map (\v -> (User $ show v, v)) _internals
