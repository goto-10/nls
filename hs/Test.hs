import Ast
import Sexp
import Test.HUnit

idt = Sexp.IdentToken
pnt n = idt (0, n)
opt = Sexp.OpToken
dmt = Sexp.DelimToken
wdt = Sexp.WordToken
int = Sexp.IntToken
wds = Sexp.WordSexp
ids = Sexp.IdentSexp
ins = Sexp.IntSexp
lis = Sexp.ListSexp

testTokenize = TestLabel "tokenize" (TestList
  [ check [pnt "foo"] "$foo"
  , check [opt "foo"] " .foo "
  , check [opt "<+>"] " <+> "
  , check [dmt ":="] " := "
  , check [wdt "foo"] " foo "
  , check [int 3] " 3 "
  , check [pnt "foo", pnt "bar", pnt "baz"] "$foo$bar$baz"
  , check [pnt "foo", pnt "bar", pnt "baz"] "$foo $bar $baz"
  , check [idt (-1, "foo"), idt (-2, "bar"), idt (-3, "baz")] "@foo @@bar @@@baz"
  , check [idt (0, "foo"), idt (1, "bar"), idt (2, "baz")] "$foo $$bar $$$baz"
  , check [dmt "(", pnt "foo", dmt ")"] "($foo)"
  ])
  where
    check expected input = TestLabel input testCase
      where
        (found, rest) = Sexp.tokenize input
        testCase = TestCase (assertEqual "" expected found)

testSexpParsing = TestLabel "sexpParsing" (TestList
  [ check (wds "foo") "foo"
  , check (ids (0, "foo")) "$foo"
  , check (ins 10) "10"
  , check (lis []) "()"
  , check (lis [wds "foo"]) "(foo)"
  , check (lis [wds "foo", wds "bar"]) "(foo bar)"
  , check (lis [wds "foo", wds "bar", wds "baz"]) "(foo bar baz)"
  , check (lis [lis [lis []]]) "((()))"
  ])
  where
    check expected input = TestLabel input testCase
      where
        found = Sexp.parse input
        testCase = TestCase (assertEqual "" expected found)

testAll = runTestTT (TestList
  [ testTokenize
  , testSexpParsing
  ])

main = testAll

