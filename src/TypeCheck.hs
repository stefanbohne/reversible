module TypeCheck where

import Prelude hiding (lookup)
import Control.Monad.State.Strict
import Control.Applicative
import Data.List hiding (lookup)
import Algebra.PartialOrd
import Algebra.Lattice
import Debug.Trace

import Result
import AST
import Context
import Eval

lin2jc :: Bool -> JanusClass
lin2jc True = JRev
lin2jc False = JFun

gt :: PartialOrd a => a -> a -> Bool
gt a b = not (a `leq` b) 
lt :: PartialOrd a => a -> a -> Bool
lt a b = b `gt` a


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

type TCContext c = (c Name Type, c Name Type)
type TCMonad c = StateT (TCContext c) Result

par :: (Context c) => (Type -> Type -> Type) -> TCMonad c a -> TCMonad c b -> TCMonad c (Bool, a, b)
par f l r = do
    (nonlin, lin) <- get
    l <- l
    (nonlinl, linl) <- get
    put (nonlin, lin)
    r <- r
    (nonlinr, linr) <- get
    let (full, lin) = joinValues f linl linr
    put (nonlin, lin)
    return (full, l, r)

localNonLin :: (Context c, Monoid (c Name Type)) => TCMonad c a -> TCMonad c a
localNonLin a = do
    (nonlin, lin) <- get
    _ <- put (nonlin <> lin, mempty)
    v <- a
    put (nonlin, lin)
    return v

getVar :: (Context c) => Name -> TCMonad c (Bool, Type)
getVar n = do
    (nonlin, lin) <- get
    lift $ ((True, ) <$> lookup lin n) <|> ((False, ) <$> lookup nonlin n)
            
pushVar :: (Context c) => Name -> Type -> TCMonad c ()
pushVar n t = do
    (nonlin, lin) <- get
    put (nonlin, update lin n t)
    return ()

popVar :: (Context c, Monoid (c Name Type)) => Name -> TCMonad c ()
popVar n = do
    (nonlin, lin) <- get
    let lin' = remove lin n
    _ <- put (nonlin, lin')
    return ()
             
typeCheckExpr' :: (Context c, Monoid (c Name Type), Monoid (c Name Value)) => Expr -> c Name Type -> Bool -> JanusClass -> Type -> Result (JanusClass, Type, c Name Type)
typeCheckExpr' e ctx fw j t = required $ do
    ((j, t, _), (nonlin, lin)) <- runStateT (typeCheck e fw j t) (ctx, mempty)
    return (j, t, lin)
                 
typeCheck :: (Context c, Monoid (c Name Type), Monoid (c Name Value)) => Expr -> Bool -> JanusClass -> Type -> TCMonad c (JanusClass, Type, [Name])
typeCheck e fw j t = lift1 (msgNewLine $ "while checking " ++ show e ++ " : " ++ show j ++ " " ++ show t) $ do
    (j', t', vs') <- typeCheck1 e fw j t
    if j' `gt` j then
        lift $ Rejected $ "expected janus class " ++ show j ++ " but inferred " ++ show j'
    else if fw then
        if t' `gt` t then
            lift $ Rejected $ "expected type " ++ show t ++ " but inferred " ++ show t'
        else
            return (j', t', vs')
    else
        if t' `lt` t then
            lift $ Rejected $ "expected type " ++ show t ++ " but inferred " ++ show t'
        else
            return (j', t', vs')
            
typeCheck1 :: forall c. (Context c, Monoid (c Name Type), Monoid (c Name Value)) => Expr -> Bool -> JanusClass -> Type -> TCMonad c (JanusClass, Type, [Name])
typeCheck1 (ELit l) fw _ _ = do
    let t = typeOfLit fw l
    return (lin2jc $ isEquType $ typeOfLit True l, t, [])

typeCheck1 (ETyped e t) fw j t2 = do
    typeCheck t True JFun TType
    t <- lift $ evalExpr' t (mempty :: c Name Value)
    t <- lift $ typeRequired $ checkType t
    (j', t', vs) <- typeCheck e fw j t
    return (j', t, vs)
            
typeCheck1 (EVar n) True _ _ = do
    (linv, tv) <- getVar n
    if linv then do
        _ <- popVar n
        return (JRev, tv, [n])
    else 
        return (lin2jc $ isEquType tv, tv, [n])
typeCheck1 (EVar n) False _ TBottom = 
    lift $ Rejected $ "Variable pattern '" ++ show n ++ "' needs type annotation"
typeCheck1 (EVar n) False _ t = do
    _ <- lift1 (expectRejected ("Variable '" ++ show n ++ "' already defined")) (getVar n)
    pushVar n t
    return (JRev, t, [n])

typeCheck1 (EApp f a) fw j t = do
    (_, tf, vsf) <- localNonLin $ typeCheck f True JFun (TFun j TBottom TTop)
    (jf, atf, rtf) <- lift $ getFunType tf
    (_, lin1) <- get
    (ja, ta, vsa) <- typeCheck a fw j atf
    (_, lin2) <- get
    case keys (without lin1 (keys lin2)) `intersect` vsf of
        [] -> return (ja \/ jf, rtf, vsf ++ vsa)
        n:_ -> lift $ Rejected $ "Variable '" ++ show n ++ "' is used in function and linearly in argument"

typeCheck1 (ERev f) fw j t = do
    (jf', tf, vsf) <- typeCheck f True JFun (if fw then TTop else TBottom)
    (jf, atf, rtf) <- lift $ getFunType tf
    if jf `leq` JRev then
        return (jf', TFun jf rtf atf, vsf)    
    else
        lift $ Rejected $ "Expected reversible function, got " ++ show (TFun jf atf rtf)

typeCheck1 (ELam p b) True _ t = do
    (j, at, rt) <- lift $ getFunType t <|> return (JFun, TBottom, TTop)
    localNonLin $ do
        (jp, tp, vsp) <- typeCheck p False JRev at
        (jb, tb, vsf) <- typeCheck b True j rt
        (_, lin) <- get
        return (JFun, TFun (jp \/ jb \/ lin2jc (isEmpty lin)) tp tb, 
            filter (\n -> find (== n) (keys lin) /= Nothing) (vsp ++ vsf))
typeCheck1 (ELam _ _) False _ _ = do
    lift $ Rejected "Lambda as pattern"

typeCheck1 (EDup e) fw _ t = do
    (je, te, vse) <- localNonLin $ typeCheck e True JFun (if fw then t else typeRev t)
    return (je \/ (lin2jc $ isEquType te), te, vse)

typeCheck1 (ECons x r) fw j t = do
    t <- lift $ getListType t <|> return (if fw then TTop else TBottom)
    if fw then do
        (jx, tx, vsx) <- typeCheck x fw j t
        (jr, TList tr, vsr) <- typeCheck r fw j (TList t)
        return (jx \/ jr, TList $ tx \/ tr, vsx ++ vsr)
    else do
        (jr, TList tr, vsr) <- typeCheck r fw j (TList t)
        (jx, tx, vsx) <- typeCheck x fw j t
        return (jx \/ jr, TList $ tx /\ tr, vsx ++ vsr)

typeCheck1 (EPair a b) fw j t = do
    (ta, tb) <- lift $ getPairType t <|> let t = if fw then TTop else TBottom in return (t, t)
    (ja, ta, jb, tb, vs) <- if fw then do
        (ja, ta, vsa) <- typeCheck a fw j ta
        (jb, tb, vsb) <- typeCheck b fw j tb
        return (ja, ta, jb, tb, vsa ++ vsb)
    else do
        (jb, tb, vsb) <- typeCheck b fw j tb
        (ja, ta, vsa) <- typeCheck a fw j ta
        return (ja, ta, jb, tb, vsa ++ vsb)
    return (ja \/ jb, TPair ta tb, vs)

typeCheck1 (EFix es) True _ t = do
    es <- forM es $ \(n, t, e) -> do
        typeCheck t True JFun TType
        t <- lift $ evalExpr' t (mempty :: c Name Value)
        t <- lift $ typeRequired $ checkType t
        return (n, t, e)
    localNonLin $ do
        (nonlin, lin) <- get
        let lin' = foldl (\lin' (n, t, e) -> update lin' n t) lin es
        put (nonlin, lin')
        tvs <- forM es $ \(n, t, e) -> do
            (_, t', vs) <- typeCheck e True JFun t
            return (t', filter (\n -> find (\(n', _ ,_) -> n' == n) es /= Nothing) vs)
        let (ts, vs) = unzip tvs
        return (JFun, tPairFold ts, concat vs)
typeCheck1 (EFix e) False _ _ = 
    lift $ Error $ "fix as pattern"

typeCheck1 (ECaseOf e []) True j t = do
    _ <- typeCheck e True j TTop
    return (JRev, TBottom, [])
typeCheck1 (ECaseOf e cs) True j t = do
    (je, te, vse) <- typeCheck e True j TTop
    let cs' = flip map cs $ \(p, v) -> do {
        (jp, tp, vsp) <- typeCheck p False (j /\ JRev) te;
        (jv, tv, vsv) <- typeCheck v True j TTop;
        return (jv \/ jp, tv, vsp ++ vsv)
    }
    (jcs, tcs, vscs) <- foldl1 f cs' 
    return (jcs, tcs, vse ++ vscs)
    where 
        f l r = do
            (full, (jl, tl, vsl), (jr, tr, vsr)) <- par (\/) l r
            return (jl \/ jr \/ lin2jc full, tl \/ tr, vsl ++ vsr)
typeCheck1 (ECaseOf e []) False j t = do
    _ <- typeCheck e False j TBottom
    return (JRev, TTop, [])
typeCheck1 (ECaseOf e cs) False j t = do
    let cs' = flip map cs $ \(p, v) -> do {
        (jv, tv, vsv) <- typeCheck v False j TBottom;
        (jp, tp, vsp) <- typeCheck p True j TTop;
        return (jv \/ jp, tv, tp, vsv ++ vsp)
    }
    (jcs, tvs, tps, vscs) <- foldl1 f cs'
    (je, te, vse) <- typeCheck e False j tvs
    return (je \/ jcs, tps, vse ++ vscs)
    where
        f l r = do
            (full, (jl, tvl, tpl, vsl), (jr, tvr, tpr, vsr)) <- par (/\) l r
            return (jl \/ jr \/ lin2jc full, tvl \/ tvr, tpl /\ tpr, vsl ++ vsr)

typeCheck1 (EFunType j at rt) True _ _ = do
    (_, _, vsat) <- typeCheck at True JFun TType
    (_, _, vsrt) <- typeCheck rt True JFun TType
    return (JFun, TType, vsat ++ vsrt)
typeCheck1 t@(EFunType _ _ _) False _ _ =
    lift $ Rejected $ "Type " ++ show t ++ " as pattern"
typeCheck1 (EPairType a b) True _ _ = do
    (_, _, vsa) <- typeCheck a True JFun TType
    (_, _, vsb) <- typeCheck b True JFun TType
    return (JFun, TType, vsa ++ vsb)
typeCheck1 t@(EPairType _ _) False _ _ =
    lift $ Rejected $ "Type " ++ show t ++ " as pattern"
typeCheck1 (EListType t) True _ _ = do
    (_, _, vst) <- typeCheck t True JFun TType
    return (JFun, TType, vst)
typeCheck1 t@(EListType _) False _ _ =
    lift $ Rejected $ "Type " ++ show t ++ " as pattern"
                
typeCheck1 e fw j t = error $ "typeCheck1: '" ++ show e ++"' " ++ show fw ++ " " ++ show j ++ " '" ++ show t ++ "'"

