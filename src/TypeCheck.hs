module TypeCheck where

import Control.Monad.State
import Control.Applicative
import Algebra.PartialOrd
import Algebra.Lattice

import Result
import AST

lin2jc :: Bool -> JanusClass
lin2jc True = JRev
lin2jc False = JFun

gt :: PartialOrd a => a -> a -> Bool
gt a b = not (a `leq` b) 
lt :: PartialOrd a => a -> a -> Bool
lt a b = b `gt` a

lift1 :: (Result a -> Result b) -> (StateT s Result a -> StateT s Result b)
lift1 f term = StateT run 
    where 
        run s = run' s (runStateT term s)
        run' s (Success (a, b)) = do
            a' <- f (Success a)
            return (a', b)
        run' s (Rejected msg) = tmp s $ f (Rejected msg)
        run' s (Error msg) = tmp s $ f (Error msg)
        run' s  (TypeError msg) = tmp s $ f (TypeError msg)
        tmp s (Success a) = Success (a, s)
        tmp s (Rejected msg) = Rejected msg
        tmp s (Error msg) = Error msg
        tmp s (TypeError msg) = TypeError msg
            

getJanusClass :: JanusClass -> JanusClass -> Result ()
getJanusClass jc jclower = 
    if jc `leq` jclower then Success ()
    else Rejected $ "expected janus class " ++ show jclower ++ " but got " ++ show jc

getFunType :: Type -> Result (JanusClass, Type, Type)
getFunType (TFun jc at rt) = Success (jc, at, rt)
getFunType t = Rejected $ "expected function type but got " ++ show t

getPairType :: Type -> Result (Type, Type)
getPairType (TPair a b) = Success (a, b)
getPairType t = Rejected $ "expected pair type but got " ++ show t

getListType :: Type -> Result Type
getListType (TList t) = Success t
getListType t = Rejected $ "expected list type but got " ++ show t

type TCContext = ([(String, Type)], [(String, Type)])
type TCMonad = StateT TCContext Result

localNonLin :: TCMonad a -> TCMonad a
localNonLin a = do
    (nonlin, lin) <- get
    _ <- put (nonlin ++ lin, [])
    v <- a
    put (nonlin, lin)
    return v

getVar :: String -> TCMonad (Bool, Type)
getVar n = do
    (nonlin, lin) <- get
    case lookup n lin of
         Just t -> return (True, t)
         Nothing -> case lookup n nonlin of
            Just t -> return (False, t)
            Nothing -> lift $ Rejected $ "Variable '" ++ n ++ "' not found"
            
pushVar :: String -> Type -> TCMonad ()
pushVar n t = do
    (nonlin, lin) <- get
    put (nonlin, (n, t) : lin)
    return ()

popVar :: String -> TCMonad ()
popVar n = do
    (nonlin, lin) <- get
    _ <- put (nonlin, filter (\(n', _) -> n' /= n) lin)
    return ()
             
typeCheckExpr :: Expr -> Result (JanusClass, Type)
typeCheckExpr e = do
    (j, t, _) <- typeCheckExpr' e preludeTypes True JFun TTop
    return (j, t)
typeCheckExpr' :: Expr -> [(String, Type)] -> Bool -> JanusClass -> Type -> Result (JanusClass, Type, [(String, Type)])
typeCheckExpr' e ctx fw j t = required $ do
    ((j, t), (nonlin, lin)) <- runStateT (typeCheck e fw j t) (ctx, [])
    return (j, t, lin)
                 
typeCheck :: Expr -> Bool -> JanusClass -> Type -> TCMonad (JanusClass, Type)
typeCheck e fw j t = lift1 (msgNewLine $ "while checking " ++ show e ++ " : " ++ show j ++ " " ++ show t) $ do
    (j', t') <- typeCheck1 e fw j t
    if j' `gt` j then
        lift $ Rejected $ "expected janus class " ++ show j ++ " but inferred " ++ show j'
    else if fw then
        if t' `gt` t then
            lift $ Rejected $ "expected type " ++ show t ++ " but inferred " ++ show t'
        else
            return (j', t')
    else
        if t' `lt` t then
            lift $ Rejected $ "expected type " ++ show t ++ " but inferred " ++ show t'
        else
            return (j', t')
            
typeCheck1 :: Expr -> Bool -> JanusClass -> Type -> TCMonad (JanusClass, Type)
typeCheck1 (ELit l) fw _ _ = do
    let t = typeOfLit fw l
    return (if isEquType $ typeOfLit True l then JRev else JFun, t)

typeCheck1 (ETyped e t) fw j t2 = do
    (j', t') <- typeCheck e fw j t
    return (j', t)
            
typeCheck1 (EVar n) True _ _ = do
    (linv, tv) <- getVar n
    if linv then do
        _ <- popVar n
        return (JRev, tv)
    else 
        return (JFun, tv)
typeCheck1 (EVar n) False _ TBottom = 
    lift $ Rejected $ "Variable pattern '" ++ n ++ "' needs type annotation"
typeCheck1 (EVar n) False _ t = do
    _ <- lift1 (expectRejected ("Variable '" ++ n ++ "' already defined")) (getVar n)
    pushVar n t
    return (JRev, t)

typeCheck1 (EApp f a) fw j t = do
    (_, tf) <- typeCheck f True JFun (TFun j TBottom TTop)
    (jf, atf, rtf) <- lift $ getFunType tf
    (ja, ta) <- typeCheck a fw j atf
    return (ja \/ jf, rtf)

typeCheck1 (ERev f) fw j t = do
    (jf', tf) <- typeCheck f True JFun (if fw then TTop else TBottom)
    (jf, atf, rtf) <- lift $ getFunType tf
    return (jf', TFun jf rtf atf)    

typeCheck1 (ELam p b) True _ t = do
    (j, at, rt) <- lift $ getFunType t <|> return (JFun, TBottom, TTop)
    localNonLin $ do
        (jp, tp) <- typeCheck p False JRev at
        (jb, tb) <- typeCheck b True j rt
        (_, lin) <- get
        return (JFun, TFun (jp \/ jb \/ lin2jc (lin == [])) tp tb)
typeCheck1 (ELam _ _) False _ _ = do
    lift $ Rejected "Lambda as pattern"

typeCheck1 (EDup e) fw _ t = do
    (je, te) <- localNonLin $ typeCheck e fw JFun t
    return (je \/ if isEquType te then JRev else JFun, te)

typeCheck1 (ECons x r) fw j t = do
    t <- lift $ getListType t <|> return (if fw then TTop else TBottom)
    if fw then do
        (jx, tx) <- typeCheck x fw j t
        (jr, TList tr) <- typeCheck r fw j (TList t)
        return (jx \/ jr, TList $ tx \/ tr)
    else do
        (jr, TList tr) <- typeCheck r fw j (TList t)
        (jx, tx) <- typeCheck x fw j t
        return (jx \/ jr, TList $ tx /\ tr)

typeCheck1 (EPair a b) fw j t = do
    (ta, tb) <- lift $ getPairType t <|> let t = if fw then TTop else TBottom in return (t, t)
    (ja, ta, jb, tb) <- if fw then do
        (ja, ta) <- typeCheck a fw j ta
        (jb, tb) <- typeCheck b fw j tb
        return (ja, ta, jb, tb)
    else do
        (jb, tb) <- typeCheck b fw j tb
        (ja, ta) <- typeCheck a fw j ta
        return (ja, ta, jb, tb)
    return (ja \/ jb, TPair ta tb)

typeCheck1 e fw j t = error $ "typeCheck1: '" ++ show e ++"' " ++ show fw ++ " " ++ show j ++ " '" ++ show t ++ "'"
    
    
