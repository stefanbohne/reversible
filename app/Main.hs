module Main where

import Prelude hiding (lookup)
import System.Console.Repline
import System.Console.Haskeline
import System.Exit
import Control.Monad.IO.Class
import Text.Megaparsec.Error
import Data.Text hiding (map)
import Control.Monad.State.Strict
import Control.Applicative

import ReplParser
import AST
import TypeCheck
import Eval
import Result
import Context
import Internals

type ReplContext = IndexList String (Type, Value)
type Repl a = HaskelineT (StateT ReplContext IO) a

resultPretty :: Result String -> String
resultPretty (Success a) = a
resultPretty (Rejected msg) = "Rejected: " ++ msg
resultPretty (Error msg) = "Error: " ++ msg
resultPretty (TypeError msg) = "Type Error: " ++ msg

resultGet :: Result a -> Repl a
resultGet (Success a) = return a
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
cmd input = case parseRepl "<repl>" $ pack input of
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
        (_, tv, _) <- resultGet $ typeCheckExpr' v tenv True JFun TTop
        (_, _, tenv') <- resultGet $ typeCheckExpr' p tenv False JRev tv
        v <- resultGet $ evalExpr' v venv
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
        _ <- liftIO $ putStrLn $ n ++ " = " ++ show v
        return ()) env
    return ()


-- Tab Completion: return a completion for partial words entered
completer :: Monad m => WordCompleter m
completer n = do
  return []

options :: [(String, [String] -> Repl ())]
options = []

ini :: Repl ()
ini = liftIO $ putStrLn "Welcome!"

main :: IO ()
main = fst <$> runStateT (evalRepl (pure "J> ") cmd options Nothing (Word completer) ini) (mapValues (\(n, v) -> (typeOfLit True v, v)) internals)