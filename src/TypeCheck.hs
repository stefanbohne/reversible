module TypeCheck where

import Prelude hiding (lookup)
import Control.Monad.State.Strict
import Control.Applicative
import Data.List hiding (lookup)
import Data.Functor.Identity
import Algebra.PartialOrd
import Algebra.Lattice
import Debug.Trace
import Control.Monad

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

getForallType :: Type -> Result (Name, Type)
getForallType (TForall n t) = Success (n, t)
getForallType t = Rejected $ "expected forall type but got " ++ show t

type TCContext c = (c Name Type, c Name Type, c Name (Maybe Type))
type TCMonad c = StateT (TCContext c) Result

par :: (Context c) => (Type -> Type -> Result Type) -> TCMonad c a -> TCMonad c b -> TCMonad c (Bool, a, b)
par f l r = do
    (types, nonlin, lin) <- get
    l <- l
    (typesl, nonlinl, linl) <- get
    put (types, nonlin, lin)
    r <- r
    (typesr, nonlinr, linr) <- get
    let oj = outerJoin linl linr
    lin <- lift $ mapValuesM (\case (_, OJB Nothing Nothing) -> Success Nothing
                                    (_, OJB Nothing (Just t)) -> Success Nothing
                                    (_, OJB (Just t) Nothing)  -> Success Nothing
                                    (_, OJB (Just tl) (Just tr)) -> (fmap Just) (f tl tr)
                                    (_, OJL _) -> Success Nothing
                                    (_, OJR _) -> Success Nothing) oj
    let full = foldValues oj True (\full -> \case (_, OJB Nothing Nothing) -> full
                                                  (_, OJB (Just _) (Just _)) -> full
                                                  (_, OJL Nothing) -> full
                                                  (_, OJR Nothing) -> full
                                                  _ -> False)
    --traceM $ "par linl " ++ show (keys linl) ++ show (values linl) ++ " linr " ++ show (keys linr) ++ show (values linr) ++ " lin " ++ show (keys lin) ++ show (values lin) ++ " full " ++ show full
    put (types, nonlin, lin)
    return (full, l, r)

localNonLin :: (Context c, Monoid (c Name Type)) => TCMonad c a -> TCMonad c a
localNonLin a = do
    (types, nonlin, lin) <- get
    put (types, nonlin <> (flatMapValues lin (\case (n, Just t) -> singletonContext n t
                                                    (_, Nothing) -> emptyContext)), emptyContext)
    v <- a
    put (types, nonlin, lin)
    return v

getVar :: (Context c) => Name -> TCMonad c (Bool, Type)
getVar n = do
    (types, nonlin, lin) <- get
    lift $ case lookup lin n of
        Success (Just t) -> Success (True, t)
        Success (Nothing) -> Rejected $ show n ++ " has already been consumed"
        Rejected _ -> (False,) <$> lookup nonlin n
        Error msg -> Error msg
        TypeError msg -> TypeError msg
            
pushVar :: (Context c) => Name -> Type -> TCMonad c ()
pushVar n t = do
    (types, nonlin, lin) <- get
    lift $ expectRejected ("Variable " ++ show n ++ " already defined") $ lookup lin n
    lift $ expectRejected ("Variable " ++ show n ++ " already defined") $ lookup nonlin n
    lift $ expectRejected ("Variable " ++ show n ++ " already defined") $ lookup types n
    put (types, nonlin, update lin n (Just t))
    return ()

popVar :: (Context c, Monoid (c Name Type)) => Name -> TCMonad c ()
popVar n = do
    (types, nonlin, lin) <- get
    let lin' = update lin n Nothing
    put (types, nonlin, lin')
    return ()

localType :: (Context c) => Name -> Type -> TCMonad c a -> TCMonad c a
localType n t a = do
    (types, nonlin, lin) <- get
    put (update types n t, update nonlin n TType, lin)
    v <- a
    put (types, nonlin, lin)
    return v

typeEval :: (Context c, Monoid (c Name Value)) => Expr -> TCMonad c Type
typeEval t = do
    (types, _, _) <- get
    v <- lift $ evalExpr' t (mapValues (\(_, t) -> VType t) types)
    t <- lift $ typeRequired $ checkType v
    return t
             
typeCheckExpr' :: (Context c, Monoid (c Name Type), Monoid (c Name (Maybe Type)), Monoid (c Name Value)) => Expr -> c Name Type -> Bool -> JanusClass -> Type -> Result (JanusClass, Type, c Name Type)
typeCheckExpr' e ctx fw j t = required $ do
    ((j, t, _), (types, nonlin, lin)) <- runStateT (typeCheck e fw j t) (mempty, ctx, mempty)
    return (j, t, flatMapValues lin (\case (n, Just t) -> singletonContext n t 
                                           (n, Nothing) -> emptyContext))
                 
typeCheck :: (Context c, Monoid (c Name Type), Monoid (c Name Value)) => Expr -> Bool -> JanusClass -> Type -> TCMonad c (JanusClass, Type, [Name])
--typeCheck e fw j t | Debug.Trace.trace (show e ++ " :<- " ++ show fw ++ " " ++ show j ++ " " ++ show t) False = undefined
typeCheck e fw j t = lift1 (msgNewLine $ "while checking " ++ show e ++ " : " ++ show j ++ " " ++ show t) $ do
    (_types, _nonlin, _lin) <- get
    --traceM $ showContext _types ++ " , " ++ showContext _nonlin ++ " , " ++ showContext _lin
    (j', t', vs') <- typeCheck1 e fw j t
    --traceM $ show e ++ " :-> " ++ show j' ++" " ++ show t' ++ " " ++ show vs'
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
    t <- typeEval t
    (j', t', vs) <- typeCheck e fw j t
    return (j', t, vs)
            
typeCheck1 (EVar n) True _ _ = do
    (linv, tv) <- getVar n
    if linv then do
        popVar n
        return (JRev, tv, [n])
    else 
        return (JFun, tv, [n])
typeCheck1 (EVar n) False _ TBottom = 
    lift $ Rejected $ "Variable pattern '" ++ show n ++ "' needs type annotation"
typeCheck1 (EVar n) False _ t = do
    pushVar n t
    return (JRev, t, [n])

typeCheck1 (EApp f a) fw j t = do
    (_, tf, vsf) <- localNonLin $ typeCheck f True JFun (TFun j TBottom TTop)
    (jf, atf, rtf) <- lift $ getFunType tf
    (_, _, lin1) <- get
    (ja, ta, vsa) <- typeCheck a fw j atf
    (_, _, lin2) <- get
    case (keys (filterValues (outerJoin lin1 lin2) $ \case
            (_, OJB (Just _) Nothing) -> True
            (n, OJL _) -> error $ "Variable " ++ show n ++ " disappeared"
            _ -> False) :: [Name]) `intersect` vsf of
        [] -> return (ja \/ jf, rtf, vsf ++ vsa)
        n : _ -> lift $ Rejected $ "Variable '" ++ show n ++ "' is used in function and linearly in argument"

typeCheck1 (ETypeApp f a) True _ t = do
    (_, ta, vsa) <- typeCheck a True JFun TType
    va' <- typeEval a
    (_, tf, vsf) <- typeCheck f True JFun (TForall (User "") t)
    (n, tf') <- lift $ typeRequired $ getForallType tf
    return (JFun, runIdentity $ subst1 (n, return va') tf', vsa ++ vsf)

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
        (_, _, lin) <- get
        let full = allValues lin (\(_, t) -> t == Nothing)
        --traceM $ "lam lin " ++ show (keys lin) ++ show (values lin) ++ " full " ++ show full
        return (JFun, TFun (jp \/ jb \/ lin2jc full) tp tb, 
            filter (\n -> find (== n) (keys lin) /= Nothing) (vsp ++ vsf))
typeCheck1 (ELam _ _) False _ _ = do
    lift $ Rejected "Lambda as pattern"

typeCheck1 (ETypeLam n b) True _ t = do
    (_, t) <- lift $ getForallType t <|> return (User "", TTop)
    (jb, tb, vsb) <- localType n (TVar n) $ typeCheck b True JFun t
    return (JFun, TForall n tb, vsb)

typeCheck1 (EDup e) fw _ t = do
    (je, te, vse) <- localNonLin $ typeCheck e True JFun (if fw then t else typeRev t)
    return (lin2jc $ isEquType te, te, vse)

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
        (types, nonlin, lin) <- get
        let lin' = foldl (\lin' (n, t, e) -> update lin' n (Just t)) lin es
        put (types, nonlin, lin')
        tvs <- forM es $ \(n, t, e) -> do
            (_, t', vs) <- typeCheck e True JFun t
            return (t', filter (\n -> find (\(n', _ ,_) -> n' == n) es /= Nothing) vs)
        let (ts, vs) = unzip tvs
        return (JFun, tPairFold ts, concat vs)
typeCheck1 (EFix e) False _ _ = 
    lift $ Error $ "fix as pattern"

typeCheck1 (ECaseOf e []) True j t = do
    typeCheck e True j TTop
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
            (full, (jl, tl, vsl), (jr, tr, vsr)) <- par (\l r -> return $ l \/ r) l r
            return (jl \/ jr \/ lin2jc full, tl \/ tr, vsl ++ vsr)
typeCheck1 (ECaseOf e []) False j t = do
    typeCheck e False j TBottom
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
            (full, (jl, tvl, tpl, vsl), (jr, tvr, tpr, vsr)) <- par (\l r -> return $ l /\ r) l r
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
typeCheck1 (EForallType n t) True _ _ = do
    (_, _, vst) <- localNonLin $ do
        pushVar n TType
        localNonLin $ typeCheck t True JFun TType
    return (JFun, TType, filter (/= n) vst)
typeCheck1 t@(EForallType _ _) False _ _ =
    lift $ Rejected $ "Type " ++ show t ++ " as pattern"
typeCheck1 (ETypeLet n t v) fw jc tv = do
    (_, _, vst) <- typeCheck t True JFun TType
    t' <- typeEval t
    localType n t' $ typeCheck v fw jc tv
                
typeCheck1 e fw j t = error $ "typeCheck1: '" ++ show e ++"' " ++ show fw ++ " " ++ show j ++ " '" ++ show t ++ "'"

