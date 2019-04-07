module Eval where

import Prelude hiding (lookup)
import qualified Prelude
import Control.Monad.Reader
import Control.Applicative
import qualified Debug.Trace

import AST
import Result
import Context

type EvalContext c = c String Value
type EvalMonad c = ReaderT (EvalContext c) Result

reverseFun :: Value -> Result Value
reverseFun (VFun p b) = Success $ VFun b p
reverseFun (VLitFun jc t1 t2 n1 f1 n2 f2) = Success $ VLitFun jc t2 t1 n2 f2 n1 f1
reverseFun v = Rejected $ (show v) ++ " is not a function"

checkList (VList l) = Success l
checkList v = Rejected $ (show v) ++ " is not a list"

checkPair (VPair a b) = Success (a, b)
checkPair v = Rejected $ (show v) ++ " is not a tuple"

checkCons (VList (a : b)) = Success (a, b)
checkCons v@(VList []) = TypeError $ (show v) ++ " is not a non-empty list"
checkCons v = Rejected $ (show v) ++ " is not a list"

evalExpr' :: (Context c) => Expr -> EvalContext c -> Result Value
evalExpr' expr ctx = runReaderT (eval expr) ctx
patternMatchExpr' :: (Context c) => Expr -> Value -> EvalContext c -> Result (EvalContext c)
patternMatchExpr' expr v ctx = runReaderT (patternMatch expr v) ctx

eval :: (Context c) => Expr -> EvalMonad c Value
eval (ELit l) = 
    return l
eval (EVar n) = do
    env <- ask
    y <- lift $ typeRequired $ lookup env n
    return y 
eval (EDup e) =
    eval e
eval (EApp f a) = do
    a' <- eval a
    f' <- eval f
    case f' of
        VFun p b -> do
            e' <- patternMatch p a'
            local (const e') $ eval b
        VLitFun _ _ _ _ f _ _ -> 
            lift $ f a'
        _ -> 
            lift $ TypeError $ "Value '" ++ show a ++ "' applied to non-function '" ++ show a' ++ "'"
eval (ERev f) = do
    f' <- eval f
    lift $ reverseFun f'
eval (ELam p b) = do
    env <- ask
    let f n = (ELit <$> lookup env n) <|> (return $ EVar n)
    p <- lift $ subst f p
    b <- lift $ subst f b
    return $ VFun p b
eval (ETyped e _) = 
    eval e
eval (EPair a b) = do
    a' <- eval a
    b' <- eval b
    return $ VPair a' b'
eval (ECons a b) = do
    a' <- eval a
    b' <- eval b
    b'' <- lift $ checkList b'
    return $ VList $ a' : b''
eval (EFix e) = do
    e' <- eval e
    mfix $ \v -> 
        case e' of
            VFun p b -> do
                env <- patternMatch p v
                local (const env) $ eval b
            VLitFun _ _ _ _ f _ _ -> 
                lift $ f v
            _ ->
                lift $ TypeError $ "fix of non-function " ++ show e'
eval (ECaseOf e cs) = do
    ve <- eval e
    let cs' = (flip map) cs $ \(p, v) -> (do
            env <- patternMatch p ve
            local (const env) $ eval v)
    foldr (<|>) (lift $ Rejected "All cases rejected") cs'

patternMatch :: (Context c) => Expr -> Value -> EvalMonad c (EvalContext c)
patternMatch (ELit l2) l1 | l1 == l2 = ask
                          | otherwise = lift $ Rejected $ "Mismatch: " ++ show l2 ++ " != " ++ show l1
patternMatch (EVar n) v = do
    env <- ask
    return $ update env n v
patternMatch (EDup e) v = do
    v' <- eval e
    if v == v' then
        ask
    else
        lift $ Rejected $ "Mismatch: " ++ show v' ++ " != " ++ show v
patternMatch (EApp f a) v = do
    f' <- eval f
    case f' of
        VFun p b -> do
            e' <- patternMatch b v
            local (const e') $ do
                p' <- eval p
                patternMatch a p'
        VLitFun _ _ _ _ _ _ f -> do
            v' <- lift $ f v
            patternMatch a v'
        l -> lift $ TypeError $ "Value '" ++ show a ++ "' applied to non-function '" ++ show f' ++ "' in pattern"
patternMatch (ERev e) _ = do
    lift $ TypeError $ "'~' as pattern"
patternMatch (ELam p b) _ = do
    lift $ TypeError $ "Lambda '" ++ show (ELam p b) ++ "' as pattern"
patternMatch (ETyped e _) v = 
    patternMatch e v
patternMatch (EPair a b) v = do
    (va, vb) <- lift $ checkPair v
    envb <- patternMatch b vb
    enva <- local (const envb) $ patternMatch a va 
    return enva
patternMatch (ECons a b) v = do
    (va, vb) <- lift $ checkCons v
    envb <- patternMatch b (VList vb)
    enva <- local (const envb) $ patternMatch a va 
    return enva
patternMatch (ECaseOf e cs) v = do
    let ys = (flip map) cs $ \(p, v') -> do {
        env <- patternMatch v' v;
        local (const env) $ do
            v <- eval p
            return (env, v)
    }
    (env, v) <- foldr (<|>) (lift $ Rejected "All cases rejected") ys 
    local (const env) $ patternMatch e v