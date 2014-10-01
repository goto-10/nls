import qualified Value as V
import qualified Sexp as S
import Test.HUnit
import qualified Eval as E

aLi = V.Literal
aIn v = aLi (vIn v)
aVa = V.Variable
aSq = V.Sequence
sId = S.Ident
sIn = S.Int
sLi = S.List
sWd = S.Word
tDm = S.DelimToken
tId = S.IdentToken
tIn = S.IntToken
tOp = S.OpToken
tPn = tId 0
tWd = S.WordToken
vIn = V.Int
vSt = V.Str
vNl = V.Null
vBn = V.Bool
fIn = E.FlatInt
fSt = E.FlatStr
fNl = E.FlatNull
fBn = E.FlatBool
fIe = E.FlatInstance
fHk = E.FlatHook

testUidStream = TestLabel "uidStream" (TestList
  [ check (i0 == i0)
  , check (not (i0 == i1))
  , check (not (i0 == i2))
  , check (not (i1 == i0))
  , check (i1 == i1)
  , check (not (i1 == i2))
  , check (not (i2 == i0))
  , check (not (i2 == i1))
  , check (i2 == i2)
  ])
  where
    check v = TestCase (assertBool "" v)
    s0 = E.uidStreamStart
    (i0, s1) = E.nextUidFromStream s0
    (i1, s2) = E.nextUidFromStream s1
    (i2, s3) = E.nextUidFromStream s2

testTokenize = TestLabel "tokenize" (TestList
  [ check [tPn "foo"] "$foo"
  , check [tOp "foo"] " .foo "
  , check [tOp "<+>"] " <+> "
  , check [tOp "!"] " ! "
  , check [tDm ":="] " := "
  , check [tDm ";", tDm ";"] " ;; "
  , check [tWd "foo"] " foo "
  , check [tIn 3] " 3 "
  , check [tPn "foo", tPn "bar", tPn "baz"] "$foo$bar$baz"
  , check [tPn "foo", tPn "bar", tPn "baz"] "$foo $bar $baz"
  , check [tId (-1) "foo", tId (-2) "bar", tId (-3) "baz"] "@foo @@bar @@@baz"
  , check [tId 0 "foo", tId 1 "bar", tId 2 "baz"] "$foo $$bar $$$baz"
  , check [tDm "(", tPn "foo", tDm ")"] "($foo)"
  ])
  where
    check expected input = TestLabel input testCase
      where
        (found, rest) = S.tokenize input
        testCase = TestCase (assertEqual "" expected found)

testSexpParsing = TestLabel "sexpParsing" (TestList
  [ check (sWd "foo") "foo"
  , check (sId 0 "foo") "$foo"
  , check (sIn 10) "10"
  , check (sLi []) "()"
  , check (sLi [sWd "foo"]) "(foo)"
  , check (sLi [sWd "foo", sWd "bar"]) "(foo bar)"
  , check (sLi [sWd "foo", sWd "bar", sWd "baz"]) "(foo bar baz)"
  , check (sLi [sLi [sLi []]]) "((()))"
  ])
  where
    check expected input = TestLabel input testCase
      where
        found = S.parseSexp input
        testCase = TestCase (assertEqual "" expected found)

testAstParsing = TestLabel "astParsing" (TestList
  [ check (aVa 0 (vSt "foo")) "$foo"
  , check (aIn 10) "10"
  , check (aLi vNl) "null"
  , check (aLi (vBn True)) "true"
  , check (aLi (vBn False)) "false"
  , check (aLi vNl) "(;)"
  , check (aIn 1) "(; 1)"
  , check (aSq [aIn 1, aIn 2]) "(; 1 2)"
  ])
  where
    check expected input = TestLabel input testCase
      where
        found = V.parseAst input
        testCase = TestCase (assertEqual "" expected found)

-- Join a list of lines into a single string. Similar to unlines but without the
-- newline char which confuses the regexps for some reason.
multiline = foldr (++) ""

testEval = TestLabel "eval" (TestList
  -- Primitive ops
  [ check fNl [] "(;)"
  , check fNl [] "null"
  , check (fBn True) [] "true"
  , check (fBn False) [] "false"
  , check (fIn 0) [] "0"
  , check (fIn 1) [] "1"
  , check (fIn 100) [] "100"
  , check (fIn 5) [] "(; 5)"
  , check (fIn 7) [] "(; 6 7)"
  , check (fIn 10) [] "(; 8 9 10)"
  -- Hooks
  , check (fHk V.LogHook) [] "$log"
  , check (fBn True) [fBn True] "(! $log true)"
  , check (fBn False) [fBn False] "(! ! $log false)"
  , check (fIn 4) [fIn 2, fIn 3, fIn 4] "(; (! $log 2) (! $log 3) (! $log 4))"
  , check (fIn 5) [] "(! + 2 3)"
  , check (fIn (-1)) [] "(! - 2 3)"
  -- Bindings
  , check (fIn 8) [] "(def $a := 8 in $a)"
  , check (fIn 9) [] "(def $a := 9 in (def $b := 10 in $a))"
  , check (fIn 12) [] "(def $a := 11 in (def $b := 12 in $b))"
  , check (fIn 13) [] "(def $a := 13 in (def $b := $a in $b))"
  , check (fIn 15) [fIn 14, fIn 15, fIn 16] (multiline
      [ "(def $a := (! $log 14) in"
      , "  (def $b := (! $log 15) in"
      , "    (; (! $log 16)"
      , "       $b)))"
      ])
  , check (fIn 18) [fIn 17] (multiline
      [ "(def $a := 17 in (;"
      , "  (! $log $a)"
      , "  (def $a := 18 in"
      , "    $a)))"
      ])
  -- Objects
  , check (fIe (V.Uid 0) V.emptyVaporInstanceState) [] "(new)"
  -- Escapes
  , check (fIn 5) [] "(with_escape $e do (! $e 5))"
  , check (fIn 6) [] "(with_escape $e do (! $log (! $e 6)))"
  , check (fIn 8) [fIn 7] (multiline
      [ "(with_escape $e do (;"
      , "  (! $log 7)"
      , "  (! $e 8)"
      , "  (! $log 9))))"
      ])
  , check (fIn 10) [fIn 10, fIn 11, fIn 10] (multiline
      [ "(! $log"
      , "  (after"
      , "    (! $log 10)"
      , "   ensure"
      , "    (! $log 11)))"
      ])
  , check (fIn 20) [fIn 12, fIn 13, fIn 16, fIn 19] (multiline
      [ "(with_escape $e do (;"
      , "  (! $log 12)"
      , "  (with_escape $f do"
      , "     (after (;"
      , "       (! $log 13)"
      , "       (! $e 14)"
      , "       (! $log 15))"
      , "      ensure (;"
      , "       (! $log 16)"
      , "       (! $f 17)"
      , "       (! $log 18))))"
      , "  (! $log 19)"
      , "  (! $e 20)"
      , "  (! $log 21)))"
      ])
  , check (fIn 26) [fIn 22, fIn 23, fIn 24, fIn 25, fIn 28, fIn 29, fIn 30] (multiline
      [ "(with_escape $e do (;"
      , "  (! $log 22)"
      , "  (after (;"
      , "    (! $log 23)"
      , "    (after (;"
      , "      (! $log 24)"
      , "      (after (;"
      , "        (! $log 25)"
      , "        (! $e 26)"
      , "        (! $log 27))"
      , "       ensure"
      , "        (! $log 28)))"
      , "     ensure"
      , "       (! $log 29)))"
      , "   ensure"
      , "     (! $log 30)))))"
      ])
  -- Failures
  , checkFail (E.UnboundVariable (vSt "foo")) [] "$foo"
  , checkFail (E.UnboundVariable (vSt "b")) [] "(def $a := 9 in $b)"
  , checkFail (E.UnboundVariable (vSt "a")) [] "(def $a := $a in $b)"
  , checkFail (E.UnboundVariable (vSt "x")) [vIn 8] (multiline
      [ "(; (! $log 8)"
      , "   $x"
      , "   (! $log 9))"
      ])
  , checkFail E.AbsentNonLocal [] "(def $f := (with_escape $e do $e) in (! $f 5))"
  ])
  where
    -- Check that evaluation succeeds.
    check expected expLog input = TestLabel input testCase
      where
        ast = V.parseAst input
        result = E.evalFlat ast
        testCase = case result of
          E.Normal (found, log) -> checkResult found log
          E.Failure cause _ -> TestCase (assertFailure ("Unexpected failure, " ++ show cause))
        checkResult found foundLog = (TestList
          [ TestCase (assertEqual "" expected found)
          , TestCase (assertEqual "" expLog foundLog)
          ])
    -- Check that evaluation fails
    checkFail expected expLog input = TestLabel input testCase
      where
        ast = V.parseAst input
        result = E.evalFlat ast
        testCase = case result of
          E.Normal (found, log) -> TestCase (assertFailure ("Expected failure, found " ++ show found))
          E.Failure cause foundLog -> checkFailure cause foundLog
        checkFailure cause foundLog = (TestList
          [ TestCase (assertEqual "" expected cause)
          , TestCase (assertEqual "" expLog foundLog)
          ])

testAll = runTestTT (TestList
  [ testTokenize
  , testSexpParsing
  , testAstParsing
  , testUidStream
  , testEval
  ])

main = testAll
