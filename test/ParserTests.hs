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

internals :: IndexList Name Value
internals = Internals.internals

parse_test :: Text -> Expr -> IO ()
parse_test src expected = 
    case parseExpr internals "<test>" src of
        Right v -> assertEqual expected v
        Left err -> fail $ errorBundlePretty err

bin op l r = EApp (EApp (ELit op) l) r

test_parseInternals = 
    forM (unIndexList internals) $ \(n, _) -> do
        parse_test (pack $ show n) (EVar n)

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
    parse_test "f~(x)~(y)~" (ERev (EApp (ERev (EApp (ERev (EVar $ User "f")) (EVar $ User "x"))) (EVar $ User "y")))

test_parseFun = do
    parse_test "\\x => 1" (ELam (EVar $ User "x") (ELit $ VInt 1))
    parse_test " \\ x + y => 2 * 3" (ELam (bin opPlus (EVar $ User "y") (EVar $ User "x")) (bin opMul (ELit $ VInt 3) (ELit $ VInt 2)))
    parse_test "\\x => \\y => x" (ELam (EVar $ User "x") (ELam (EVar $ User "y") (EVar $ User "x")))
    parse_test "\\x : Int => x : Int" (ELam (ETyped (EVar $ User "x") (ELit $ VType TInt)) (ETyped (EVar $ User "x") (ELit $ VType TInt)))
    parse_test "\\f(x) => f(x)" (ELam (EApp (EVar $ User "f") (EVar $ User "x")) (EApp (EVar $ User "f") (EVar $ User "x")))
    parse_test "(\\a => b)(c)" (EApp (ELam (EVar $ User "a") (EVar $ User "b")) (EVar $ User "c"))

test_parseType = do
    parse_test "x : Int" (ETyped (EVar $ User "x") (ELit $ VType TInt))
    parse_test "x : Int -> (Int) <=> ()" (ETyped (EVar $ User "x") (EFunType JFun (ELit $ VType TInt) (EFunType JRev (ELit $ VType TInt) (ELit $ VType TUnit))))
    parse_test "x : Int <=> [Bool] -> (String, Char)" (ETyped (EVar $ User "x") (EFunType JFun (EFunType JRev (ELit $ VType TInt) (EListType (ELit $ VType TBool))) (EPairType (ELit $ VType TString) (ELit $ VType TChar))))

test_parseTyped = do
    parse_test "x + y : Int" (bin opPlus (ETyped (EVar $ User "y") (ELit $ VType TInt)) (EVar $ User "x"))
    parse_test "x : Int -> Int" (ETyped (EVar $ User "x") (EFunType JFun (ELit $ VType TInt) (ELit $ VType TInt)))

test_parseDup = do
    parse_test "&x" (EDup (EVar $ User "x"))
    parse_test "&[]" (EDup (ELit $ VList []))
    parse_test "&123" (EDup (ELit $ VInt 123))
    parse_test "&x:Int" (ETyped (EDup (EVar $ User "x")) (ELit $ VType TInt))
    parse_test "&x+y" (bin opPlus (EVar $ User "y") (EDup (EVar $ User "x")))
    parse_test "&f(&x)" (EApp (EDup (EVar $ User "f")) (EDup (EVar $ User "x")))

test_parseTuple = do
    parse_test "()" (ELit VUnit)
    parse_test "(a)" (EVar $ User "a")
    parse_test "(1,b)" (EPair (ELit $ VInt 1) (EVar $ User "b"))
    parse_test "(1,2,3,4)" (ePairFold [ELit $ VInt 1, ELit $ VInt 2, ELit $ VInt 3, ELit $ VInt 4])

test_parseList = do
    parse_test "[]" (ELit $ VList [])
    parse_test "[a]" (ECons (EVar $ User "a") (ELit $ VList []))
    parse_test "[1,b]" (ECons (ELit $ VInt 1) (ECons (EVar $ User "b") (ELit $ VList [])))
    parse_test "[1,2,3,4]" (ECons (ELit $ VInt 1) (ECons (ELit $ VInt 2) (ECons (ELit $ VInt 3) (ECons (ELit $ VInt 4) (ELit $ VList [])))))
    parse_test "a::b" (ECons (EVar $ User "a") (EVar $ User "b"))
    parse_test "\\a+1::b:Int::c=>d:Int::e" (
        ELam(ECons (EApp (EApp (ELit opPlus) (ELit $ VInt 1)) (EVar $ User "a")) (
             ECons (ETyped (EVar $ User "b") (ELit $ VType TInt)) (EVar $ User "c")))
            (ECons (ETyped (EVar $ User "d") (ELit $ VType TInt)) (EVar $ User "e"))
        )
    parse_test "[[[]]]" (ECons (ECons (ELit $ VList []) (ELit $ VList [])) (ELit $ VList []))
    
test_parseFix = do
    parse_test "fix()" (EFix [])
    parse_test "fix(x: Int = y, y: Int = x)" (EFix [(User "x", (ELit $ VType TInt), EVar $ User "y"), (User "y", (ELit $ VType TInt), EVar $ User "x")])

test_parseLet = do
    parse_test "let 1=2; 3=4 in 5" (ECaseOf (ELit $ VInt 2) [(ELit $ VInt 1, ECaseOf (ELit $ VInt 4) [(ELit $ VInt 3, ELit $ VInt 5)])])
    parse_test "\\let a=b in c => d" (ELam (ECaseOf (EVar $ User "b") [(EVar $ User "a", EVar $ User "c")]) (EVar $ User "d"))
    parse_test "(\\let a=b in c => d)(x)" (EApp (ELam (ECaseOf (EVar $ User "b") [(EVar $ User "a", EVar $ User "c")]) (EVar $ User "d")) (EVar $ User "x"))

test_parseCase = do
    parse_test "case 1 of" (ECaseOf (ELit $ VInt 1) [])
    parse_test "case 1 of 2 => 3" (ECaseOf (ELit $ VInt 1) [(ELit $ VInt 2, ELit $VInt 3)])
    parse_test "case 1 of 2 => 3; 4 => 5" (ECaseOf (ELit $ VInt 1) [
        (ELit $ VInt 2, ELit $VInt 3), (ELit $ VInt 4, ELit $ VInt 5)])

test_parseForall = do
    parse_test "(forall A. x: A) : forall A. A" (ETyped (ETypeLam (User "A") (ETyped (EVar $ User "x") (EVar $ User "A"))) (EForallType (User "A") (EVar $ User "A")))