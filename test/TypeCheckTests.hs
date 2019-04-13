{-# OPTIONS_GHC -F -pgmF htfpp #-}
module TypeCheckTests where

import Data.Text
import Test.Framework hiding (Success)
import Text.Megaparsec.Error
import Control.Monad

import Parser
import AST
import Result
import TypeCheck
import qualified Internals
import Internals hiding (internals)
import Context

internals :: IndexList String Value
internals = Internals.internals
internalTypes :: IndexList String Type
internalTypes = mapValues (typeOfLit True . snd) internals

tcTest :: Text -> (JanusClass, Text) -> IO ()
tcTest src (expectedJ, expectedSrc) = do
    case parseExpr internals "<src>" src of
        Right expr -> case parseType internals "<expectedSrc>" expectedSrc of
            Right expectedT -> tcTestExpr expr (expectedJ, expectedT)
            Left err -> fail $ errorBundlePretty err
        Left err -> fail $ errorBundlePretty err
tcTestExpr :: Expr -> (JanusClass, Type) -> IO ()
tcTestExpr expr expected = do
    let tc = (\(j, t, lin) -> (j, t)) <$> typeCheckExpr' expr internalTypes True JFun TTop
    assertEqual (Success expected) tc
tcTestFail :: Text -> IO ()
tcTestFail src = do
    case parseExpr internals "<src>" src of
        Right expr -> tcTestFailExpr expr
        Left err -> fail $ errorBundlePretty err
tcTestFailExpr :: Expr -> IO ()
tcTestFailExpr expr = do
    case required $ typeCheckExpr' expr internalTypes True JFun TTop of
        Error _ -> return ()
        res -> assertEqual (Error "*anything*") res
            
test_internals = 
    forM (unIndexList internals) $ \(n, v) ->
        let t = typeOfLit True v in
        tcTestExpr (EVar n) (lin2jc (isEquType t), t)

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
    tcTest "\\x:Int => &x" (JFun, "Int -> Int")
    tcTest "\\x:Int => 1" (JFun, "Int -> Int")
    tcTest "(\\x => x) : Int -> Int" (JFun, "Int -> Int")
    tcTestFail "\\x => x"
    tcTest "\\x: Int => \\y: [Int] => y" (JFun, "Int -> [Int] <=> [Int]")
    tcTest "\\f: Int <=> Int => \\f(x) => x" (JFun, "Int <=> Int -> Int <=> Int")
    tcTestFail "\\f: Int -> Int <=> Int => \\x: Int => f(&x)(x)"
    tcTest "\\f: Int -> Int <=> Int => \\x: Int => f(x)(&x)" (JFun, "(Int -> Int <=> Int) -> Int -> Int")
    tcTest "\\f: Int -> Int <=> Int => \\x: Int => f(&x)(&x)" (JFun, "(Int -> Int <=> Int) -> Int -> Int")

test_rev = do
    tcTest "(\\x: Int => x)~" (JFun, "Int <=> Int")
    tcTestFail "(\\x: Int => &x)~"

test_dup = do
    tcTest "&1" (JRev, "Int")
    tcTest "\\x: Int => &x" (JFun, "Int -> Int")
    tcTest "\\x: Int => \\ &x => ()" (JFun, "Int -> Int <=> ()")

test_tuple = do
    tcTest "()" (JRev, "()")
    tcTest "(1, 2)" (JRev, "(Int, Int)")
    tcTest "(1, [1], \\x: Int => x)" (JFun, "(Int, [Int], Int <=> Int)")

test_list = do
    tcTest "\\[] => []" (JFun, "[Top] <=> [Bottom]")
    tcTest "\\[\"x\", \'x\'] => [1,True]" (JFun, "[Bottom] <=> [Top]")
    tcTest "\\[[[]]] => [[[]]]" (JFun, "[[[Top]]] <=> [[[Bottom]]]")
    tcTest "\\[1] => [1]" (JFun, "[Int] <=> [Int]")
    tcTest "\\[1, 2, 3] => [1, 2, 3]" (JFun, "[Int] <=> [Int]")
    tcTestFail "\\x: Int => [x, x]"
    tcTest "\\x: Int => [&x, x]" (JFun, "Int <=> [Int]")

test_fix = do
    tcTest "fix()" (JFun, "()")
    tcTest "fix(x: Int = 1)" (JFun, "Int")
    tcTest "fix(x: Int = x)" (JFun, "Int")
    tcTest "fix(f: Int <=> Int = \\x => f(x + 1))" (JFun, "Int <=> Int")
    tcTestFail "fix(f: Int <=> Int = \\x => f(&x + 1))"
    tcTest "fix(append: ([Int], Int) <=> [Int] = \\(l: [Int], x: Int) => case l of [] => [x]; y::l => y::append(l, x))" (JFun, "([Int], Int) <=> [Int]")

test_let = do
    tcTest "\\let n = m + 1 in n - 1 => m" (JFun, "Int <=> Int")
    tcTestFail "\\let n = m + 1 in n - 1 => n"

test_case = do
    tcTest "\\case () of => case () of" (JFun, "Top <=> Bottom")
    tcTest "case 1 of 1 => 1; 2 => 2" (JRev, "Int")
    tcTest "case 1 of 1 => 1; 2 => \"\"" (JRev, "Top")
    tcTestFail "case 1 of 1 => 1; \"\" => \"\""
    tcTestFail "\\n: Int => case n of 1 => n"
    tcTestFail "\\n: Int => case 1 of n => 1"
    tcTest "case 1 of n => n; m => m" (JRev, "Int")
    tcTest "case 1 of n => n; m => &m" (JFun, "Int")
    tcTest "case 1 of n => &n; m => m" (JFun, "Int")
    tcTest "\\x: Int => case 1 of 1 => x; 2 => x" (JFun, "Int <=> Int")
    tcTest "\\x: Int => case 1 of 1 => x; 2 => 2" (JFun, "Int -> Int")
    tcTest "case 1 of 1 => \\x: Int => x; 2 => \\x: Int => &x" (JFun, "Int -> Int")    