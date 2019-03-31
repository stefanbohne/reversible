module Main where

import System.Console.Repline
import System.Console.Haskeline
import System.Exit
import Control.Monad.IO.Class
import Data.List
import Text.Megaparsec.Error
import Data.Text hiding (map)
import Control.Monad.State.Strict
import Control.Applicative

import ReplParser
import AST
import TypeCheck
import Eval
import Result

type ReplContext = [(String, (Type, Value))]
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
runCmd (EvalCmd e) = liftIO $ putStrLn $ resultPretty $ show <$> evalExpr e
runCmd (LetCmd p v) = do
        env <- lift $ get
        let tenv = map (\(n, (t, v)) -> (n, t)) env
        let venv = map (\(n, (t, v)) -> (n, v)) env
        (_, tv, _) <- resultGet $ typeCheckExpr' v tenv True JFun TTop
        (_, _, tenv') <- resultGet $ typeCheckExpr' p tenv False JRev tv
        v <- resultGet $ evalExpr' v venv
        venv' <- resultGet $ patternMatchExpr' p v (venv :: EvalContext)
        env' <- resultGet $ mapM (\(n, t) -> do
            v <- lookup n venv'
            return (n, (t, v))) tenv'
        _ <- put (env' ++ env)
        return ()
    where
        lookup n l = case Prelude.lookup n l of
            Just v -> Success v
            Nothing -> TypeError $ "Variable " ++ n ++ " not found in venv"
runCmd (TypeCmd e) = do
    env <- get
    let tenv = map (\(n, (t, v)) -> (n, t)) env
    (j, t, _) <- resultGet $ typeCheckExpr' e tenv True JFun TTop
    _ <- liftIO $ putStrLn $ show j ++ ": " ++ show t
    return ()
runCmd (ListCmd) = do
    env <- get
    forM_ env $ \(n, (t, v)) ->
        liftIO $ putStrLn $ n ++ " = " ++ show v


-- Tab Completion: return a completion for partial words entered
completer :: Monad m => WordCompleter m
completer n = do
  return []

options :: [(String, [String] -> Repl ())]
options = []

ini :: Repl ()
ini = liftIO $ putStrLn "Welcome!"

main :: IO ()
main = fst <$> runStateT (evalRepl (pure "J> ") cmd options Nothing (Word completer) ini) (map (\(n ,v) -> (n, (typeOfLit True v, v))) prelude)