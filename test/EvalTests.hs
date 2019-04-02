{-# OPTIONS_GHC -F -pgmF htfpp #-}
module EvalTests where

import Data.Text
import Test.Framework hiding (Success)
import Text.Megaparsec.Error

import Parser
import AST
import Eval
import Result
import Internals
import Context

internals_ :: IndexList String Value
internals_ = internals

evalTest :: Text -> Value -> IO ()
evalTest src expected = do
    case parseExpr "<test>" src of
        Right expr -> assertEqual (Success expected) (evalExpr' expr internals_)
        Left err -> fail $ errorBundlePretty err

evalTestRejected :: Text -> IO ()
evalTestRejected src = do
    case parseExpr "<test>" src of
        Right expr -> case evalExpr' expr internals_ of
            Rejected _ -> return ()
        Left err -> fail $ errorBundlePretty err
        
test_lit = do
    evalTest "10" $ VInt 10
    evalTest "\\x => x" $ VFun (EVar "x") (EVar "x")

test_arithmatic = do
    evalTest "1+2" $ VInt 3
    evalTest "1-2*3" $ VInt (-5)
    evalTest "5 / 2" $ VInt 2

test_lambda = do
    evalTest "(\\x => \\y => y) (21)" $ VFun (EVar "y") (EVar "y")
    evalTest "(\\1 => 2) (1)" $ VInt 2
    evalTestRejected "(\\1 => 1) (2)"

test_pair = do
    evalTest "(12, 30)" $ VPair (VInt 12) (VInt 30)
    evalTest "(\\(a, b) => a + b) (12, 30)" $ VInt 42

test_list = do
    evalTest "[1,2,3]" $ VList [VInt 1, VInt 2, VInt 3]
    evalTest "(\\[a,b,c] => a + b * c) ([2, 4, 10])" $ VInt 42

test_concat = do
    evalTest "\"123\" ++ \"321\"" $ VString "123321"

test_splitAt = do
    evalTest "splitAt(1)(\"123\")" $ VPair (VString "1") (VString "23")
    evalTest "splitAt(4)(\"123\")" $ VPair (VString "123") (VString "")
    evalTest "splitAt(0)(\"123\")" $ VPair (VString "") (VString "123")
    evalTest "splitAt(0)(\"\")" $ VPair (VString "") (VString "")
    evalTest "splitAt(1)(\"\")" $ VPair (VString "") (VString "")
    evalTest "splitAt(1)~(\"1\", \"23\")" $ VString "123"
    evalTest "splitAt(4)~(\"\", \"123\")" $ VString "123"
    evalTest "splitAt(0)~(\"123\", \"\")" $ VString "123"
    evalTest "splitAt(0)~(\"\", \"\")" $ VString ""