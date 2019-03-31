module Eval where

import Prelude hiding (lookup)
import qualified Prelude
import Control.Monad.Reader

import AST
import Result

type EvalMonad = ReaderT EvalContext Result

def :: String -> Value -> EvalContext
def n v = [(n, v)]

lookup :: EvalContext -> String -> Result Value
lookup ctx n = case Prelude.lookup n ctx  of
    Just v -> Success v
    Nothing -> Rejected $ "Variable '" ++ n ++ "' is not defined"

evalExpr :: Expr -> Result Value
evalExpr expr = evalExpr' expr (prelude)
evalExpr' :: Expr -> EvalContext -> Result Value
evalExpr' expr ctx = runReaderT (eval expr) ctx
patternMatchExpr' :: Expr -> Value -> EvalContext -> Result EvalContext
patternMatchExpr' expr v ctx = runReaderT (patternMatch expr v) ctx

eval :: Expr -> EvalMonad Value
eval (ELit l) = return l
eval (EVar n) = do
    env <- ask
    lift $ typeRequired $ lookup env n
eval (EApp f a) = do
    a' <- eval a
    f' <- eval f
    case f' of
        VFun e p b -> local (const e) $ do
            e' <- patternMatch p a'
            local (const e') $ eval b
        VLitFun _ _ _ _ f _ _ -> 
            lift $ f a'
        VInt i -> lift $ TypeError $ "Value '" ++ show a ++ "' applied to non-function '" ++ show a' ++ "'"
eval (ERev f) = do
    f' <- eval f
    lift $ reverseFun f'
eval (ELam p b) = do
    env <- ask
    return $ VFun env p b
eval (ELet p v s) = do
    v' <- eval v
    env2 <- patternMatch p v'
    local (const env2) $ eval s
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

patternMatch :: Expr -> Value -> EvalMonad EvalContext
patternMatch (ELit l2) l1 | l1 == l2 = ask
                          | otherwise = lift $ Rejected $ "Mismatch: " ++ show l2 ++ " != " ++ show l1
patternMatch (EVar n) v = do
    env <- ask
    return $ def n v <> env
patternMatch (EApp f a) v = do
    f' <- eval f
    case f' of
        VFun e p b -> local (const e) $ do
            e' <- patternMatch b v
            local (const e') $ do
                p' <- eval p
                patternMatch a p'
        VLitFun _ _ _ _ _ _ f -> do
            v' <- lift $ f v
            patternMatch a v'
        l -> lift $ TypeError $ "Value '" ++ show a ++ "' applied to non-function '" ++ show f' ++ "' in pattern"
patternMatch (ELam p b) _ = do
    lift $ TypeError $ "Lambda '" ++ show (ELam p b) ++ "' as pattern"
patternMatch (ELet p v s) x = do
    env2 <- patternMatch s x
    local (const env2) $ do
        p' <- eval p
        patternMatch v p'
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