{-# OPTIONS_GHC -F -pgmF htfpp #-}
module TypeCheckTests where

import Data.Text
import Test.Framework hiding (Success)
import Text.Megaparsec.Error

import Parser
import AST
import Result
import TypeCheck
import Internals
import Context

internalTypes = mapValues (typeOfLit True . snd) (internals :: IndexList String Value)

tcTest :: Text -> (JanusClass, Text) -> IO ()
tcTest src (expectedJ, expectedSrc) = do
    case parseExpr "<src>" src of
        Right expr -> case parseType "<expectedSrc>" expectedSrc of
            Right expectedT -> tcTestExpr expr (expectedJ, expectedT)
            Left err -> fail $ errorBundlePretty err
        Left err -> fail $ errorBundlePretty err
tcTestExpr :: Expr -> (JanusClass, Type) -> IO ()
tcTestExpr expr expected = do
    let tc = (\(j, t, lin) -> (j, t)) <$> typeCheckExpr' expr internalTypes True JFun TTop
    assertEqual (Success expected) tc
tcTestFail :: Text -> IO ()
tcTestFail src = do
    case parseExpr "<src>" src of
        Right expr -> tcTestFailExpr expr
        Left err -> fail $ errorBundlePretty err
tcTestFailExpr :: Expr -> IO ()
tcTestFailExpr expr = do
    case required $ typeCheckExpr' expr internalTypes True JFun TTop of
        Error _ -> return ()
        res -> assertEqual (Error "*anything*") res
            
test_int = do
    tcTest "123" (JRev, "Int")
    tcTest "123: Int" (JRev, "Int")
    tcTestFail "123: [Int]"
    tcTestFail "123: Int -> Int"
    tcTestFail "123: Int <=> Int"
    tcTestFail "123: ()"
    tcTestFail "123: (Int, Int)"

test_string = do
    tcTest "\"\"" (JRev, "String")

test_char = do
    tcTest "\'\\'\'" (JRev, "Char")
    
test_app = do
    tcTestExpr (ELit opPlus) (JFun, TFun JFun TInt (TFun JRev TInt TInt))
    tcTestExpr (EApp (ELit opPlus) (ELit $ VInt 1)) (JFun, TFun JRev TInt TInt)
    tcTest "1+2" (JRev, "Int")
    tcTest "(\\splitAt(1)(s) => 1)(\"12\", \"3\")" (JFun, "Int")
    tcTest "(\\splitAt(1)~(a, b) => 1)(\"123\")" (JFun, "Int")
    
test_lam = do
    tcTest "\\x:Int => x" (JFun, "Int <=> Int")
    tcTest "\\x:Int => 1" (JFun, "Int -> Int")
    tcTest "(\\x => x) : Int -> Int" (JFun, "Int -> Int")
    tcTestFail "\\x => x"
    tcTest "\\x: Int => \\y: [Int] => y" (JFun, "Int -> [Int] <=> [Int]")
    tcTest "\\f: Int <=> Int => \\f(x) => x" (JFun, "Int <=> Int -> Int <=> Int")

test_dup = do
    tcTest "&1" (JRev, "Int")
    tcTest "\\x: Int => &x" (JFun, "Int -> Int")

test_tuple = do
    tcTest "()" (JRev, "()")
    tcTest "(1, 2)" (JRev, "(Int, Int)")
    tcTest "(1, [1], \\x: Int => x)" (JFun, "(Int, [Int], Int <=> Int)")

test_list = do
    tcTest "\\[] => []" (JFun, "[Top] <=> [Bottom]")
    tcTest "\\[\"x\", \'x\'] => [1,True]" (JFun, "[Bottom] -> [Top]")
    tcTest "\\[[[]]] => [[[]]]" (JFun, "[[[Top]]] <=> [[[Bottom]]]")
    tcTest "\\[1] => [1]" (JFun, "[Int] <=> [Int]")
    tcTest "\\[1, 2, 3] => [1, 2, 3]" (JFun, "[Int] <=> [Int]")
    tcTestFail "\\x: Int => [x, x]"
    tcTest "\\x: Int => [&x, x]" (JFun, "Int -> [Int]")

test_fix = do
    tcTest "\\\\x: Int => 1" (JFun, "Int")
    tcTest "\\\\x: Int => x" (JFun, "Int")
    tcTest "\\\\f: Int <=> Int => \\x: Int => f(x + 1)" (JFun, "Int <=> Int")    