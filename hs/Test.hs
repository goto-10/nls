import Ast
import Sexp
import Test.HUnit
import Eval

aLi = Ast.Literal
aIn v = aLi (vIn v)
aVa = Ast.Variable
aSq = Ast.Sequence
sId = Sexp.IdentSexp
sIn = Sexp.IntSexp
sLi = Sexp.ListSexp
sWd = Sexp.WordSexp
tDm = Sexp.DelimToken
tId = Sexp.IdentToken
tIn = Sexp.IntToken
tOp = Sexp.OpToken
tPn = tId 0
tWd = Sexp.WordToken
vIn = Ast.IntValue
vSt = Ast.StrValue
vNl = Ast.NullValue
vBn = Ast.BoolValue

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
    s0 = Eval.uidStreamStart
    (i0, s1) = Eval.nextUidFromStream s0
    (i1, s2) = Eval.nextUidFromStream s1
    (i2, s3) = Eval.nextUidFromStream s2

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
        (found, rest) = Sexp.tokenize input
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
        found = Sexp.parse input
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
        found = Ast.parse input
        testCase = TestCase (assertEqual "" expected found)

testAll = runTestTT (TestList
  [ testTokenize
  , testSexpParsing
  , testAstParsing
  , testUidStream
  ])

main = testAll

