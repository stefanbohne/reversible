module Result where

import Control.Applicative
import Control.Monad.Fail
import Control.Monad.Fix
import Control.Monad.Reader
import Control.Monad.State
import Data.Monoid
import qualified Debug.Trace


data Result a = 
        Success a
    |   Suspended (Result a)
    |   Rejected String
    |   Error String
    |   TypeError String
    deriving (Show, Eq)
force :: Result a -> Result a
force (Suspended (Suspended a)) = force a
force (Suspended a) = a
force a = a
instance Functor Result where
    fmap f (Success x) = Success $ f x
    fmap f (Suspended x) = Suspended $ fmap f x
    fmap f (Rejected s) = Rejected s
    fmap f (Error s) = Error s
    fmap f (TypeError s) = TypeError s
instance Applicative Result where
    pure = Success
    (Success f) <*> (Success x) = Success $ f x
    (Suspended f) <*> (Success x) = Suspended $ force f <*> Success x
    (Success f) <*> (Suspended x) = Suspended $ (Success f) <*> force x
    (Suspended f) <*> (Suspended x) = Suspended $ force f <*> force x
    _ <*> (TypeError s) = TypeError s
    (TypeError s) <*> _ = TypeError s
    _ <*> (Error s) = Error s
    (Error s) <*> _ = Error s
    _ <*> (Rejected s) = Rejected s
    (Rejected s) <*> _ = Rejected s
instance Monad Result where
    (Success x) >>= f = f x
    (Suspended a) >>= f = Suspended $ a >>= f
    Rejected s >>= f = Rejected s
    Error s >>= f = Error s
    TypeError s >>= f = TypeError s
instance MonadFail Result where
    fail msg = error msg
instance Alternative Result where
    empty = Rejected "undefined"
    (Success x) <|> _ = Success x
    (Suspended x) <|> y = (Suspended $ x <|> y)
    x <|> (Suspended y) = (Suspended $ x <|> y)
    (Rejected msg1) <|> (Rejected msg2) = Rejected $ msg1 ++ " OR " ++ msg2
    (Rejected _) <|> y = y
    x <|> _ = x
instance MonadFix Result where
    mfix f = let x = f (unSuccess x) in x
        where unSuccess (Success v) = v

trace :: (Monad m) => String -> b -> m b 
trace x y = return $ Debug.Trace.trace x y

class AsResult f where
    asResult :: String -> f a -> Result a
instance AsResult Maybe where
    asResult _ (Just a) = (Success a)
    asResult msg Nothing = Rejected msg

class Temporary f where
    temporarily :: f a -> f a
instance Temporary Result where
    temporarily x = x
instance Temporary (ReaderT e m) where
    temporarily x = x
instance (Monad m) => Temporary (StateT s m) where
    temporarily x = do
        s <- get
        y <- x
        put s
        return y

getResult :: Result a -> a
getResult (Success a) = a
getResult (Rejected msg) = error msg
getResult (Error msg) = error msg
getResult (TypeError msg) = error msg

required :: Result a -> Result a
required (Rejected s) = Error s
required x = x

typeRequired :: Result a -> Result a
typeRequired (Rejected s) = TypeError s
typeRequired x = x

expectRejected :: String -> Result a -> Result ()
expectRejected _ (Rejected _) = Success ()
expectRejected msg (Success v) = Rejected msg
expectRejected _ (Error msg) = Error msg
expectRejected _ (TypeError msg) = TypeError msg

msgPrefix :: String -> Result a -> Result a
msgPrefix prefix (Rejected msg) = Rejected (prefix ++ msg)
msgPrefix prefix (Error msg) = Error (prefix ++ msg)
msgPrefix prefix (TypeError msg) = TypeError (prefix ++ msg)
msgPrefix _ r = r

msgNewLine :: String -> Result a -> Result a
msgNewLine line (Rejected msg) = Rejected (msg ++ "\n" ++ line)
msgNewLine line (Error msg) = Error (msg ++ "\n" ++ line)
msgNewLine line (TypeError msg) = TypeError (msg ++ "\n" ++ line)
msgNewLine _ r = r
