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
  , check [tDm ":="] " := "
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
  , check (aLi vNl) "(begin)"
  , check (aIn 1) "(begin 1)"
  , check (aSq [aIn 1, aIn 2]) "(begin 1 2)"
  ])
  where
    check expected input = TestLabel input testCase
      where
        found = V.parseAst input
        testCase = TestCase (assertEqual "" expected found)

testEval = TestLabel "eval" (TestList
  [ check fNl [] "(begin)"
  , check fNl [] "null"
  , check (fBn True) [] "true"
  , check (fBn False) [] "false"
  , check (fIn 0) [] "0"
  , check (fIn 1) [] "1"
  , check (fIn 100) [] "100"
  , check (fIn 5) [] "(begin 5)"
  , check (fIn 7) [] "(begin 6 7)"
  , check (fIn 10) [] "(begin 8 9 10)"
  , check (fIn 8) [] "(def $a := 8 in $a)"
  , check (fIn 9) [] "(def $a := 9 in (def $b := 10 in $a))"
  , check (fIn 12) [] "(def $a := 11 in (def $b := 12 in $b))"
  , check (fIn 13) [] "(def $a := 13 in (def $b := $a in $b))"
  , check (fIe (V.Uid 0) V.emptyVaporInstanceState) [] "(new)"
  , checkFail (E.UnboundVariable (vSt "foo")) [] "$foo"
  , checkFail (E.UnboundVariable (vSt "b")) [] "(def $a := 9 in $b)"
  , checkFail (E.UnboundVariable (vSt "a")) [] "(def $a := $a in $b)"
  ])
  where
    -- Check that evaluation succeeds.
    check expected log input = TestLabel input testCase
      where
        ast = V.parseAst input
        result = E.evalFlat ast
        testCase = TestCase (case result of
          E.Normal found -> assertEqual "" expected found
          E.Failure cause -> assertFailure ("Unexpected failure, " ++ show cause))
    -- Check that evaluation fails
    checkFail expected log input = TestLabel input testCase
      where
        ast = V.parseAst input
        result = E.evalFlat ast
        testCase = TestCase (case result of
          E.Normal found -> assertFailure ("Expected failure, found " ++ show found)
          E.Failure cause -> assertEqual "" expected cause)

testAll = runTestTT (TestList
  [ testTokenize
  , testSexpParsing
  , testAstParsing
  , testUidStream
  , testEval
  ])

main = testAll
