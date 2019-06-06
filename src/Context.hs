module Context where

import Result
import Debug.Trace
import Data.List (find, filter, intercalate)
import Data.Functor.Identity

data OuterJoin a = OJL a
                 | OJR a
                 | OJB a a

class Context c where
    emptyContext :: c k v 
    singletonContext :: (Eq k) => k -> v -> c k v
    singletonContext k v = update emptyContext k v
    copyContext :: (Context c2, Eq k) => c k v -> c2 k v
    copyContext c = foldValues c emptyContext $ \res (k, v) -> update res k v
    lookup :: (Eq k, Show k) => c k v -> k -> Result v
    update :: (Eq k) => c k v -> k -> v -> (c k v)
    remove :: (Eq k) => c k v -> k -> c k v
    isEmpty :: c k v -> Bool
    isEmpty c = case keys c of [] -> True; _ -> False
    keys :: c k v -> [k]
    keys c = foldValues c [] (\l (k, v) -> l ++ [k])
    values :: c k v -> [v]
    values c = foldValues c [] (\l (k, v) -> l ++ [v])
    keyValues :: c k v -> [(k, v)]
    keyValues c = foldValues c [] (\l (k, v) -> l ++ [(k, v)])
    foldValues :: c k v -> a -> (a -> (k, v) -> a) -> a
    allValues :: c k v -> ((k, v) -> Bool) -> Bool
    allValues c f = foldValues c True (\res (k, v) -> res && f (k, v))
    filterValues :: (Eq k) => c k v -> ((k, v) -> Bool) -> c k v
    filterValues c f = foldValues c emptyContext (\res (k, v) -> if f (k, v) then update res k v else res)
    mapValues :: (Eq k) => ((k, v) -> v') -> c k v -> c k v'
    mapValues f l = runIdentity $ mapValuesM (return . f) l
    mapValuesM :: (Monad m, Eq k) => ((k, v) -> m v') -> c k v -> m (c k v')
    mapValuesM f l = flatMapValuesM (return l) (\(k, v) -> do
        v' <- f (k, v)
        return $ update emptyContext k v')
    joinValues :: (Show k, Show v, Eq k) => (v -> v -> v) -> (c k v) -> (c k v) -> (Bool, c k v)
    joinValues f l r = runIdentity $ joinValuesM (\v1 v2 -> return $ f v1 v2) l r
    joinValuesM :: (Monad m, Eq k) => (v -> v -> m v) -> (c k v) -> (c k v) -> m (Bool, c k v)
    joinValuesM f l r = do
        let oj = outerJoin l r
        joined <- mapValuesM g oj
        let full = foldValues oj True h
        return (full, joined)
        where g (_, OJB v1 v2) = f v1 v2
              g (_, OJL v1) = return v1
              g (_, OJR v2) = return v2
              h full (_, OJB _ _) = full
              h _ _ = False
    flatMapValues :: c k v -> ((k, v) -> c k2 v2) -> c k2 v2
    flatMapValues l f = runIdentity $ flatMapValuesM (return l) (return . f)
    flatMapValuesM :: (Monad m) => m (c k v) -> ((k, v) -> m (c k2 v2)) -> m (c k2 v2)
    without :: (Eq k) => c k v -> [k] -> c k v 
    without l keys = flatMapValues l (\(k, v) -> 
        if (find (== k) keys) == Nothing then emptyContext
        else update emptyContext k v)
    outerJoin :: (Eq k) => c k v -> c k v -> c k (OuterJoin v)
    showContext :: (Show v, Show k) => c k v -> String
    showContext c = "[" ++ intercalate ", " (map (\(k, v) -> show k ++ "->" ++ show v) (keyValues c)) ++ "]"
instance {-# OVERLAPPABLE #-} (Context c, Show k, Show v) => Show (c k v) where
    show = showContext
instance {-# OVERLAPPABLE #-} (Context c, Eq k, Eq v) => Eq (c k v) where
    c1 == c2 = foldValues (outerJoin c1 c2) True $ \res -> \case 
            (_, OJB v1 v2) -> res && v1 == v2
            _ -> False
newtype IndexList a b = IndexList { unIndexList :: [(a, b)] }
instance Context IndexList where
    emptyContext = IndexList []
    lookup (IndexList c) k = asResult ("Undefined " ++ show k) $ Prelude.lookup k c
    update c k v = let IndexList c' = remove c k in
                   IndexList $ (k, v) : c'
    remove (IndexList c) k = IndexList $ filter (\(k', _) -> k' /= k) c
    foldValues (IndexList []) a f = a
    foldValues (IndexList ((k, v) : r)) a f = foldValues (IndexList r) (f a (k, v)) f
    flatMapValuesM l f = do
        IndexList l <- l
        case l of
            [] -> return $ IndexList []
            x : r -> do
                IndexList l' <- f x
                IndexList r' <- flatMapValuesM (return $ IndexList r) f
                return $ IndexList $ concat [l', r']
    outerJoin (IndexList []) (IndexList []) = 
        IndexList []
    outerJoin (IndexList []) (IndexList ((k, v) : r)) = 
        update (outerJoin (IndexList []) (IndexList r)) k (OJR v)
    outerJoin (IndexList ((k, v) : l)) (IndexList r) =
        case findIndex_ k r of 
            Just (v2, r') -> update (outerJoin (IndexList l) (IndexList r')) k (OJB v v2)
            Nothing -> update (outerJoin (IndexList l) (IndexList r)) k (OJL v)
findIndex_ :: (Eq a) => a -> [(a, b)] -> Maybe (b, [(a, b)])
findIndex_ a [] = Nothing
findIndex_ a ((a', b') : r) | a == a' = Just (b', r)
                            | otherwise = case findIndex_ a r of
                                Nothing -> Nothing
                                Just (b'', r) -> Just (b'', (a', b') : r)
instance Semigroup (IndexList a b) where
    (IndexList a) <> (IndexList b) = IndexList $ a <> b
instance Monoid (IndexList a b) where
    mempty = IndexList mempty


mkContext :: (Context c, Eq k) => [(k, v)] -> c k v
mkContext [] = emptyContext
mkContext ((k, v) : c) = update (mkContext c) k v 