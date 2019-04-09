{-# OPTIONS_GHC -F -pgmF htfpp #-}
module ParserTests where

import Data.Text
import Test.Framework
import Text.Megaparsec.Error
import Control.Monad

import Parser
import AST
import Context
import qualified Internals
import Internals hiding (internals)

internals :: IndexList String Value
internals = Internals.internals

parse_test :: Text -> Expr -> IO ()
parse_test src expected = 
    case parseExpr internals "<test>" src of
        Right v -> assertEqual expected v
        Left err -> fail $ errorBundlePretty err

bin op l r = EApp (EApp (ELit op) l) r

test_parseInternals = 
    forM (unIndexList internals) $ \(n, _) -> do
        parse_test (pack n) (EVar n)

test_parseInt = do
    parse_test "1" (ELit $ VInt 1)
    parse_test "   10   " (ELit $ VInt 10)
    parse_test "  (  (  123 ) ) " (ELit $ VInt 123)

test_parseString = do
    parse_test "\"\"" (ELit $ VString "")
    parse_test "\"\\\"\\'\\n \"" (ELit $ VString "\"'\n ")
    parse_test "\"1\" ++ \"2\" ++ \"3\"" $ bin opConcat (ELit $ VString "3") (bin opConcat (ELit $ VString "2") (ELit $ VString "1"))

test_parseChar = do
    parse_test "'\\0'" (ELit $ VChar '\0')
    parse_test "' '" (ELit $ VChar ' ')
    parse_test "'\\t'" (ELit $ VChar '\t')

test_parseBinOp = do
    parse_test "1+2" (bin opPlus (ELit $ VInt 2) (ELit $ VInt 1))
    parse_test "1-2" (bin opMinus (ELit $ VInt 2) (ELit $ VInt 1))
    parse_test "1*2" (bin opMul (ELit $ VInt 2) (ELit $ VInt 1))
    parse_test "1/2" (bin opDiv (ELit $ VInt 2) (ELit $ VInt 1))
    parse_test "0+1*(2-3)/4+5" (
            bin opPlus (
                ELit $ VInt 5) (
                bin opPlus (
                    bin opDiv (
                        ELit $ VInt 4) (
                        bin opMul (
                            bin opMinus (ELit $ VInt 3) (ELit $ VInt 2)) (
                            ELit $ VInt 1))) (
                    ELit $ VInt 0)))

test_parseRev = do
    parse_test "f~(x)~(y)~" (ERev (EApp (ERev (EApp (ERev (EVar "f")) (EVar "x"))) (EVar "y")))

test_parseFun = do
    parse_test "\\x => 1" (ELam (EVar "x") (ELit $ VInt 1))
    parse_test " \\ x + y => 2 * 3" (ELam (bin opPlus (EVar "y") (EVar "x")) (bin opMul (ELit $ VInt 3) (ELit $ VInt 2)))
    parse_test "\\x => \\y => x" (ELam (EVar "x") (ELam (EVar "y") (EVar "x")))
    parse_test "\\x : Int => x : Int" (ELam (ETyped (EVar "x") TInt) (ETyped (EVar "x") TInt))
    parse_test "\\f(x) => f(x)" (ELam (EApp (EVar"f") (EVar "x")) (EApp (EVar "f") (EVar "x")))
    parse_test "(\\a => b)(c)" (EApp (ELam (EVar "a") (EVar "b")) (EVar "c"))

test_parseType = do
    parse_test "x : Int" (ETyped (EVar "x") TInt)
    parse_test "x : Int -> (Int) <=> ()" (ETyped (EVar "x") (TFun JFun TInt (TFun JRev TInt TUnit)))
    parse_test "x : Int <=> [Bool] -> (String, Char)" (ETyped (EVar "x") (TFun JFun (TFun JRev TInt (TList TBool)) (TPair TString TChar)))

test_parseTyped = do
    parse_test "x + y : Int" (bin opPlus (ETyped (EVar "y") TInt) (EVar "x"))
    parse_test "x : Int -> Int" (ETyped (EVar "x") (TFun JFun TInt TInt))

test_parseDup = do
    parse_test "&x" (EDup (EVar "x"))
    parse_test "&[]" (EDup (ELit $ VList []))
    parse_test "&123" (EDup (ELit $ VInt 123))
    parse_test "&x:Int" (ETyped (EDup (EVar "x")) TInt)
    parse_test "&x+y" (bin opPlus (EVar "y") (EDup (EVar "x")))
    parse_test "&f(&x)" (EApp (EDup (EVar "f")) (EDup (EVar "x")))

test_parseTuple = do
    parse_test "()" (ELit VUnit)
    parse_test "(a)" (EVar "a")
    parse_test "(1,b)" (EPair (ELit $ VInt 1) (EVar "b"))
    parse_test "(1,2,3,4)" (ePairFold [ELit $ VInt 1, ELit $ VInt 2, ELit $ VInt 3, ELit $ VInt 4])

test_parseList = do
    parse_test "[]" (ELit $ VList [])
    parse_test "[a]" (ECons (EVar "a") (ELit $ VList []))
    parse_test "[1,b]" (ECons (ELit $ VInt 1) (ECons (EVar "b") (ELit $ VList [])))
    parse_test "[1,2,3,4]" (ECons (ELit $ VInt 1) (ECons (ELit $ VInt 2) (ECons (ELit $ VInt 3) (ECons (ELit $ VInt 4) (ELit $ VList [])))))
    parse_test "a::b" (ECons (EVar "a") (EVar "b"))
    parse_test "\\a+1::b:Int::c=>d:Int::e" (
        ELam(ECons (EApp (EApp (ELit opPlus) (ELit $ VInt 1)) (EVar "a")) (
             ECons (ETyped (EVar "b") TInt) (EVar "c")))
            (ECons (ETyped (EVar "d") TInt) (EVar "e"))
        )
    parse_test "[[[]]]" (ECons (ECons (ELit $ VList []) (ELit $ VList [])) (ELit $ VList []))
    
test_parseFix = do
    parse_test "fix()" (EFix [])
    parse_test "fix(x: Int = y, y: Int = x)" (EFix [("x", TInt, EVar "y"), ("y", TInt, EVar "x")])

test_parseLet = do
    parse_test "let 1=2; 3=4 in 5" (ECaseOf (ELit $ VInt 2) [(ELit $ VInt 1, ECaseOf (ELit $ VInt 4) [(ELit $ VInt 3, ELit $ VInt 5)])])
    parse_test "\\let a=b in c => d" (ELam (ECaseOf (EVar "b") [(EVar "a", EVar "c")]) (EVar "d"))
    parse_test "(\\let a=b in c => d)(x)" (EApp (ELam (ECaseOf (EVar "b") [(EVar "a", EVar "c")]) (EVar "d")) (EVar "x"))

test_parseCase = do
    parse_test "case 1 of" (ECaseOf (ELit $ VInt 1) [])
    parse_test "case 1 of 2 => 3" (ECaseOf (ELit $ VInt 1) [(ELit $ VInt 2, ELit $VInt 3)])
    parse_test "case 1 of 2 => 3; 4 => 5" (ECaseOf (ELit $ VInt 1) [
        (ELit $ VInt 2, ELit $VInt 3), (ELit $ VInt 4, ELit $ VInt 5)])