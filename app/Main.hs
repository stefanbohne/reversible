module Main where

import Prelude hiding (lookup, readFile)
import System.Console.Repline
import System.Console.Haskeline
import System.Exit
import Control.Monad.IO.Class
import Text.Megaparsec.Error
import Data.Text hiding (map, foldl, foldr)
import Data.Text.IO (readFile)
import Control.Monad.State.Strict
import Control.Exception (try)
import Debug.Trace
import Paths_reversible

import ReplParser
import FileParser
import AST
import TypeCheck
import Eval
import Result
import Context
import qualified Internals

data ReplContext = ReplContext { 
    ctxTypes :: IndexList Name Type, 
    ctxValues :: IndexList Name (Type, Value)
}
type Repl a = HaskelineT (StateT ReplContext IO) a
getTypes = lift $ ctxTypes <$> get
putTypes :: IndexList Name Type -> Repl ()
putTypes x = lift $ get >>= (\c -> return $ c { ctxTypes = x }) >>= put
getValues = lift $ ctxValues <$> get
putValues :: IndexList Name (Type, Value) -> Repl ()
putValues x = lift $ get >>= (\c -> return $ c { ctxValues = x }) >>= put
internals :: IndexList Name Value
internals = Internals.internals

resultPretty :: Result String -> String
resultPretty (Success a) = a
resultPretty (Suspended a) = resultPretty a
resultPretty (Rejected msg) = "Rejected: " ++ msg
resultPretty (Error msg) = "Error: " ++ msg
resultPretty (TypeError msg) = "Type Error: " ++ msg

resultGet :: Result a -> Repl a
resultGet (Success a) = return a
resultGet (Suspended a) = resultGet a
resultGet (Rejected msg) = do
    liftIO $ putStrLn $ "Rejected: " ++ msg
    abort
resultGet (Error msg) = do
    liftIO $ putStrLn $ "Error: " ++ msg
    abort
resultGet (TypeError msg) = do
    liftIO $ putStrLn $ "Type Error: " ++ msg
    abort

-- Evaluation : handle each line user inputs
cmd :: String -> Repl ()
cmd input = case parseRepl internals "<repl>" $ pack input of
    Left err -> liftIO $ putStrLn $ errorBundlePretty err
    Right cmd -> runCmd cmd
runCmd :: ReplCmd -> Repl ()
runCmd (QuitCmd) = liftIO $ do
    putStrLn "Goodbye."
    exitSuccess 
runCmd (EvalCmd e) = do 
    types <- getTypes
    env <- getValues
    let tenv = mapValues (\(n, (t, v)) -> t) env
    let venv = mapValues (\(n, (t, v)) -> v) env
    (_, _, _) <- resultGet $ typeCheckExpr' e types tenv True JFun TTop
    liftIO $ putStrLn $ resultPretty $ show <$> evalExpr' e venv
runCmd (LetCmd p v) = do
    types <- getTypes
    env <- getValues
    let tenv = mapValues (\(n, (t, v)) -> t) env
    let venv = mapValues (\(n, (t, v)) -> v) env
    let v' = (case p of
                ETyped (EVar n) t -> EFix [(n, t, v)]
                _ -> v)
    (_, tv, _) <- resultGet $ typeCheckExpr' v' types tenv True JFun TTop
    (_, _, tenv') <- resultGet $ typeCheckExpr' p types tenv False JRev tv
    v <- resultGet $ evalExpr' v' venv
    venv' <- resultGet $ patternMatchExpr' p v (venv :: EvalContext IndexList)
    env' <- resultGet $ mapValuesM (\(n, t) -> do
        v <- lookup venv' n
        return (t, v)) tenv'
    putValues (env' <> env)
    return ()
runCmd (TypeLetCmd n t) = do
    ReplContext {..} <- get
    (_, _, _) <- resultGet $ typeCheckExpr' t ctxTypes (mapValues (\(n, t) -> TType) ctxTypes) True JFun TType
    v <- resultGet $ evalExpr' t (mapValues (\(n, t) -> VType t) ctxTypes) >>= checkType
    put ReplContext { ctxTypes = update ctxTypes n v, .. }
runCmd (TypeCmd e) = do
    types <- getTypes
    env <- getValues
    let tenv = mapValues (\(n, (t, v)) -> t) env
    (j, t, _) <- resultGet $ typeCheckExpr' e types tenv True JFun TTop
    liftIO $ putStrLn $ show j ++ ": " ++ show t
    return ()
runCmd (ListCmd) = do
    types <- getTypes
    mapValuesM (\(n, t) -> do
        liftIO $ putStrLn $ "type " ++ show n ++ " = " ++ show t
        return ()) types
    env <- getValues
    mapValuesM (\(n, (t, v)) -> do
        liftIO $ putStrLn $ show n ++ " = " ++ show v
        return ()) env
    return ()
runCmd (LoadCmd f) = do
    text <- liftIO $ try (readFile f)
    case text of
        Right text -> case parseFile internals f text of
            Left err -> liftIO $ putStrLn $ errorBundlePretty err
            Right lines -> do
                let types = [(n, t) | TypeLine n t <- lines]
                forM types $ \(n, t) -> runCmd(TypeLetCmd (User n) t)
                let lets = [(n, t, e) | LetLine n t e <- lines]
                let p = ePairFold $ map (\(n, t, _) -> ETyped (EVar $ User n) t) lets
                let vs = EFix $ map (\(n, t, e) -> (User n, t, e)) lets
                runCmd (LetCmd p vs)
                return ()
        Left exc ->
            liftIO $ putStrLn $ "Error opening '" ++ f ++ "': " ++ show (exc :: IOException)

-- Tab Completion: return a completion for partial words entered
completer :: Monad m => WordCompleter m
completer n = do
  return []

help args = do
    liftIO $ putStrLn "Help!"

options :: [(String, [String] -> Repl ())]
options = []

ini :: Repl ()
ini = do
    prelude <- liftIO $ getDataFileName "prelude.rev"
    runCmd (LoadCmd prelude)
    liftIO $ putStrLn "Welcome!"

main :: IO ()
main = fst <$> runStateT (evalRepl (pure "J> ") cmd options Nothing (Word completer) ini)  ReplContext {..}
    where 
        ctxTypes = emptyContext :: IndexList Name Type
        ctxValues = mapValues (\(n, v) -> (typeOfLit True v, v)) internals