{-# OPTIONS_GHC -F -pgmF htfpp #-}
module EvalTests where

import Data.Text
import Test.Framework hiding (Success)
import Text.Megaparsec.Error
import Control.Monad

import Parser
import AST
import Eval
import Result
import qualified Internals
import Context

internals :: IndexList Name Value
internals = Internals.internals

evalTest :: Text -> Value -> IO ()
evalTest src expected = do
    case parseExpr internals "<test>" src of
        Right expr -> assertEqual (Success expected) (evalExpr' expr internals)
        Left err -> fail $ errorBundlePretty err

evalTestRejected :: Text -> IO ()
evalTestRejected src = do
    case parseExpr internals "<test>" src of
        Right expr -> case evalExpr' expr internals of
            Rejected _ -> return ()
        Left err -> fail $ errorBundlePretty err
        
test_internals = 
    forM (unIndexList internals) $ \(n, v) ->
        evalTest (pack $ show n) v

test_lit = do
    evalTest "10" $ VInt 10
    evalTest "\\x => x" $ VFun internals (EVar $ User "x") (EVar $ User "x")

test_arithmatic = do
    evalTest "1+2" $ VInt 3
    evalTest "1-2*3" $ VInt (-5)
    evalTest "5 / 2" $ VInt 2

test_lambda = do
    evalTest "\\x -> \\y <=> y" $ VFun internals (EVar $ User "x") (ELam (Just JRev) (EVar $ User "y") (EVar $ User "y"))
    evalTest "(\\x => \\y => y) (21)" $ VFun (update internals (User "x") (VInt 21)) (EVar $ User "y") (EVar $ User "y")
    evalTest "(\\1 => 2) (1)" $ VInt 2
    evalTestRejected "(\\1 => 1) (2)"
    evalTest "(\\f: (Int, Int) -> Int => \\x: Int => f(&x + 1, x + 2))(\\(x,y) => x * y)(3)" $ VInt 20

test_rev = do
    evalTest "(\\x: Int => x+1)~(43)" $ VInt 42
    evalTest "(\\(\\x: Int => x + 1)~(x) => x)(41)" $ VInt 42

test_dup = do
    evalTest "(\\x: Int => (&x, x))(42)" $ VPair (VInt 42) (VInt 42)
    evalTest "(\\(&x, x: Int) => x)(42, 42)" $ VInt 42

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

test_fix = do
    evalTest "fix()" $ VUnit
    evalTest "fix(x: Int = 1)" $ VInt 1
    evalTest "let fac = fix(fac: Int -> Int = \\n: Int => case n of 0 => 1; n => n * fac(n - 1)) in (fac(0), fac(1), fac(5))" $ vPairFold [VInt 1, VInt 1, VInt 120]
    evalTest "(fix(append: ([Int], Int) <=> [Int] = \\(l: [Int], x: Int) => case l of [] => [x]; y::l => y::append(l, x)))([1,2],3)" $ VList [VInt 1, VInt 2, VInt 3]
    evalTest "(fix(append: ([Int], Int) <=> [Int] = \\(l: [Int], x: Int) => case l of [] => [x]; y::l => y::append(l, x)))~([1,2,3])" $ VPair (VList [VInt 1, VInt 2]) (VInt 3)
    evalTest "let (append, reverse) = fix(\
        \append: forall A. ([A], A) <=> [A] = forall A. \\(l: [A], x: A) => case l of [] => [x]; y::l => y::append{A}(l, x), \
        \reverse: forall A. [A] <=> [A] = forall A. \\l => case l of [] => []; append{A}(reverse{A}(r), x) => x::r) in \
        \(reverse{Int}([1,2,3]), reverse{Int}~([1,2,3]))" (VPair (VList [VInt 3, VInt 2, VInt 1]) (VList [VInt 3, VInt 2, VInt 1]))
    evalTest "fix(times: Int -> (Int -> Int) -> (Int -> Int) = \
        \\\n => \\f => \\m => case n of 0 => m; n2 + 1 => times(n2)(f)(f(m)))(10)(\\x => x + 2)(3)" (VInt 23)

test_case = do
    evalTest "case 1 of 1 => 2; 2 => 3" $ VInt 2
    evalTest "case 2 of 1 => 2; 2 => 3" $ VInt 3
    evalTest "(\\let n = m / 2 in n + 1 => let l - 1 = m / 2 in l)(42)" $ VInt 42