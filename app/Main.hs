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
import Control.Applicative
import Control.Exception (try)
import Paths_reversible

import ReplParser
import FileParser
import AST
import TypeCheck
import Eval
import Result
import Context
import qualified Internals

type ReplContext = IndexList Name (Type, Value)
type Repl a = HaskelineT (StateT ReplContext IO) a
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
    _ <- liftIO $ putStrLn $ "Rejected: " ++ msg
    abort
resultGet (Error msg) = do
    _ <- liftIO $ putStrLn $ "Error: " ++ msg
    abort
resultGet (TypeError msg) = do
    _ <- liftIO $ putStrLn $ "Type Error: " ++ msg
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
    env <- lift $ get
    let tenv = mapValues (\(n, (t, v)) -> t) env
    let venv = mapValues (\(n, (t, v)) -> v) env
    (_, _, _) <- resultGet $ typeCheckExpr' e tenv True JFun TTop
    liftIO $ putStrLn $ resultPretty $ show <$> evalExpr' e venv
runCmd (LetCmd p v) = do
    env <- lift $ get
    let tenv = mapValues (\(n, (t, v)) -> t) env
    let venv = mapValues (\(n, (t, v)) -> v) env
    let v' = (case p of
                ETyped (EVar n) t -> EFix [(n, t, v)]
                _ -> v)
    (_, tv, _) <- resultGet $ typeCheckExpr' v' tenv True JFun TTop
    (_, _, tenv') <- resultGet $ typeCheckExpr' p tenv False JRev tv
    v <- resultGet $ evalExpr' v' venv
    venv' <- resultGet $ patternMatchExpr' p v (venv :: EvalContext IndexList)
    env' <- resultGet $ mapValuesM (\(n, t) -> do
        v <- lookup venv' n
        return (t, v)) tenv'
    _ <- put (env' <> env)
    return ()
runCmd (TypeCmd e) = do
    env <- lift $ get
    let tenv = mapValues (\(n, (t, v)) -> t) env
    (j, t, _) <- resultGet $ typeCheckExpr' e tenv True JFun TTop
    _ <- liftIO $ putStrLn $ show j ++ ": " ++ show t
    return ()
runCmd (ListCmd) = do
    env <- lift $ get
    _ <- mapValuesM (\(n, (t, v)) -> do
        _ <- liftIO $ putStrLn $ show n ++ " = " ++ show v
        return ()) env
    return ()
runCmd (LoadCmd f) = do
    text <- liftIO $ try (readFile f)
    case text of
        Right text -> case parseFile internals f text of
            Left err -> liftIO $ putStrLn $ errorBundlePretty err
            Right lets -> do
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
main = fst <$> runStateT (evalRepl (pure "J> ") cmd options Nothing (Word completer) ini) (mapValues (\(n, v) -> (typeOfLit True v, v)) internals)