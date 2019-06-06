module Eval where

import Prelude hiding (lookup)
import qualified Prelude
import Control.Monad.Reader
import Control.Applicative
import qualified Debug.Trace

import AST
import Result
import Context

type EvalContext c = c Name Value
type EvalMonad c = ReaderT (EvalContext c) Result

unfix :: (Context c, Monoid (c Name Value)) => Value -> EvalMonad c Value
unfix (VFix e es) = do
    local (\env -> foldl (\env (n, e) -> update env n (VFix e es)) mempty es) $ eval e
unfix v = return v

reverseFun :: Value -> Result Value
reverseFun (VFix _ _) = error "missing unfix"
reverseFun (VFun env p b) = Success $ VFun env b p
reverseFun (VLitFun (TFun jc at rt) n1 f1 n2 f2) = Success $ VLitFun (TFun jc rt at) n2 f2 n1 f1
reverseFun v = Rejected $ (show v) ++ " is not a function"

checkList (VList l) = Success l
checkList (VFix _ _) = error "missing unfix"
checkList v = Rejected $ (show v) ++ " is not a list"

checkPair (VPair a b) = Success (a, b)
checkPair (VFix _ _) = error "missing unfix"
checkPair v = Rejected $ (show v) ++ " is not a tuple"

checkCons (VList (a : b)) = Success (a, b)
checkCons (VFix _ _) = error "missing unfix"
checkCons v@(VList []) = TypeError $ (show v) ++ " is not a non-empty list"
checkCons v = Rejected $ (show v) ++ " is not a list"

checkType (VType t) = Success t
checkType (VFix _ _) = error "missing unfix"
checkType v = Rejected $ (show v) ++ " is not a type"

evalExpr' :: (Context c, Monoid (c Name Value)) => Expr -> EvalContext c -> Result Value
evalExpr' expr ctx = runReaderT (eval expr) ctx
patternMatchExpr' :: (Context c, Monoid (c Name Value)) => Expr -> Value -> EvalContext c -> Result (EvalContext c)
patternMatchExpr' expr v ctx = runReaderT (patternMatch expr v) ctx

eval :: (Context c, Monoid (c Name Value)) => Expr -> EvalMonad c Value
--eval e | Debug.Trace.trace (show e ++ " ~>") False = undefined
eval e = do
    _env <- ask
    --Debug.Trace.traceM $ showContext _env
    v <- eval1 e >>= unfix 
    --Debug.Trace.trace (show e ++ " ~> " ++ show v) $ return ()
    return v

eval1 :: (Context c, Monoid (c Name Value)) => Expr -> EvalMonad c Value
eval1 (ELit l) =  
    return l
eval1 (EVar n) = do
    env <- ask
    y <- lift $ typeRequired $ lookup env n
    return y 
eval1 (EDup e) =
    eval e
eval1 (EApp f a) = do
    a' <- eval a
    f' <- eval f
    case f' of
        VFun env p b -> local (\_ -> copyContext env) $ do
            e' <- patternMatch p a'
            local (const e') $ eval b
        VLitFun _ _ f _ _ -> 
            lift $ f a'
        VFix _ _ ->
            error "missing unfix"
        _ -> 
            lift $ TypeError $ "Value '" ++ show a ++ "' applied to non-function '" ++ show a' ++ "'"
eval1 (ERev f) = do
    f' <- eval f
    lift $ reverseFun f'
eval1 (ELam p b) = do
    env <- ask
    return $ VFun (copyContext env) p b
eval1 (EPair a b) = do
    a' <- eval a
    b' <- eval b
    return $ VPair a' b'
eval1 (ECons a b) = do
    a' <- eval a
    b' <- eval b
    b'' <- lift $ checkList b'
    return $ VList $ a' : b''
eval1 (EFix es) = do
    env <- ask
    let f n = rejectedToNothing (ELit <$> lookup env n)
    es <- forM es $ \(n, _, e) -> do
        e <- lift $ subst f e
        return (n, e)
    vs <- forM es $ \(n, e) ->
        return $ VFix e es 
    return $ vPairFold vs
eval1 (ECaseOf e cs) = do
    ve <- eval e
    let cs' = (flip map) cs $ \(p, v) -> (do
            env <- patternMatch p ve
            local (const env) $ eval v)
    foldr (<|>) (lift $ Rejected "All cases rejected") cs'
eval1 (EFunType j at rt) = do
    at' <- eval at >>= lift . checkType
    rt' <- eval rt >>= lift . checkType
    return $ VType $ TFun j at' rt'
eval1 (EPairType a b) = do
    a' <- eval a >>= lift . checkType
    b' <- eval b >>= lift . checkType
    return $ VType $ TPair a' b'
eval1 (EListType t) = do
    t' <- eval t >>= lift . checkType
    return $ VType $ TList t'
eval1 (EForallType n t) = do
    t' <- (local (\env -> update env n (VType $ TVar n)) (eval t)) >>= lift . checkType
    return $ VType $ TForall n t'
eval1 (ETypeLam n b) = do
    eval b
eval1 (ETyped e _) = 
    eval e
eval1 (ETypeApp f a) = 
    eval1 f
eval1 (ETypeLet _ _ v) =
    eval1 v
    
patternMatch :: (Context c, Monoid (c Name Value)) => Expr -> Value -> EvalMonad c (EvalContext c)
--patternMatch e v | Debug.Trace.trace (show e ++ " <~ " ++ show v) False = undefined
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
        VFun env p b -> do
            p' <- local (\_ -> copyContext env) $ do
                env' <- patternMatch b v
                local (const env') $ eval p
            patternMatch a p'
        VLitFun _ _ _ _ f -> do
            v' <- lift $ f v
            patternMatch a v'
        VFix _ _ -> 
            error "missing unfix"
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