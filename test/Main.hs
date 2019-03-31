{-# OPTIONS_GHC -F -pgmF htfpp #-}
module Main where

import Test.Framework
import {-@ HTF_TESTS @-} ParserTests
import {-@ HTF_TESTS @-} EvalTests
import {-@ HTF_TESTS @-} TypeCheckTests

main = htfMain htf_importedTests
