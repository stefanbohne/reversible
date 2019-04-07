module Context where

import Result
import Debug.Trace

class Context c where
    lookup :: (Eq k) => c k v -> k -> Result v
    update :: c k v -> k -> v -> (c k v)
    remove :: (Eq k) => c k v -> k -> c k v
    isEmpty :: c k v -> Bool
    mapValues :: ((k, v) -> v') -> c k v -> c k v'
    mapValuesM :: (Monad m) => ((k, v) -> m v') -> c k v -> m (c k v')
    joinValues :: (Show k, Show v, Eq k) => (v -> v -> v) -> (c k v) -> (c k v) -> (Bool, c k v)
instance (Context c) => Functor (c a) where
    fmap f = mapValues (\(k, v) -> f v)
newtype IndexList a b = IndexList { unIndexList :: [(a, b)] }
    deriving (Eq, Show)
instance Context IndexList where
    lookup (IndexList c) k = asResult "Undefined" $ Prelude.lookup k c
    update (IndexList c) k v = IndexList $ (k, v) : c
    remove (IndexList c) k = IndexList $ filter (\(k', _) -> k' /= k) c
    isEmpty (IndexList []) = True
    isEmpty _ = False
    mapValues f (IndexList c) = IndexList $ fmap (\(k, v) -> (k, f (k, v))) c
    mapValuesM f (IndexList c) = IndexList <$> mapM (\(k, v) -> do
                                    v' <-  f (k, v)
                                    return (k, v')) c
    joinValues f (IndexList []) (IndexList r) = (null r, IndexList [])
    joinValues f (IndexList ((k, v) : r)) (IndexList l) = 
        let (full, joined) = joinValues f (IndexList r) (IndexList l) in
        case Prelude.lookup k l of
            Just v2 -> (full, IndexList $ (k, f v v2) : unIndexList joined)
            Nothing -> (False, joined)
instance Semigroup (IndexList a b) where
    (IndexList a) <> (IndexList b) = IndexList $ a <> b
instance Monoid (IndexList a b) where
    mempty = IndexList mempty


mkContext :: (Context c, Monoid (c k v)) => [(k, v)] -> c k v
mkContext [] = mempty
mkContext ((k, v) : c) = update (mkContext c) k v