import Test.HUnit
import qualified Data.Map as Map
import qualified Value as V
import qualified Sexp as S
import qualified Eval as E
import qualified Method as M

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

testEvalExpr = TestLabel "evalExpr" (TestList
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

testMatchOrder = TestLabel "matchOrder" (TestList
  [ check (M.ScoreEq < M.ScoreIs 0)
  , check (M.ScoreIs 0 < M.ScoreIs 1)
  , check (M.ScoreIs 100 < M.ScoreIs 101)
  , check (M.ScoreIs 65536 < M.ScoreAny)
  ])
  where
    check v = TestCase (assertBool "" v)

-- An inheritance hiararchy that only gives nontrivial types to ints and where
-- the relationship between types is described explicitly by the map below.
data TestHierarchy = TestHierarchy

testInheritance = Map.fromList (
  -- 2 <: 1 <: 0
  [ (2, [1])
  , (1, [0])
  -- 14 <: 13 <: 12 <: 11 <: 0, also 14 <: 2 <: 1 <: 0
  , (14, [13, 2])
  , (13, [12])
  , (12, [11])
  , (11, [0])
  ])

instance M.TypeHierarchy TestHierarchy where
  typeOf _ (V.Int n) = V.Uid n
  typeOf _ _ = V.Uid 0
  superTypes _ (V.Uid n) = map V.Uid (Map.findWithDefault [] n testInheritance)

testSingleGuards = TestLabel "singleGuards" (TestList
  [ check M.ScoreAny M.Any (V.Str "foo")
  , check M.ScoreAny M.Any (V.Int 0)
  , check M.ScoreAny M.Any V.Null
  , check M.ScoreAny M.Any (V.Bool True)
  , check M.ScoreNone (M.Eq V.Null) (V.Str "foo")
  , check M.ScoreNone (M.Eq V.Null) (V.Int 0)
  , check M.ScoreEq (M.Eq V.Null) V.Null
  , check (M.ScoreIs 0) (M.Is (V.Uid 2)) (V.Int 2)
  , check (M.ScoreIs 1) (M.Is (V.Uid 1)) (V.Int 2)
  , check (M.ScoreIs 2) (M.Is (V.Uid 0)) (V.Int 2)
  , check M.ScoreNone (M.Is (V.Uid 2)) (V.Int 1)
  , check (M.ScoreIs 0) (M.Is (V.Uid 1)) (V.Int 1)
  , check (M.ScoreIs 1) (M.Is (V.Uid 0)) (V.Int 1)
  , check M.ScoreNone (M.Is (V.Uid 2)) (V.Int 0)
  , check M.ScoreNone (M.Is (V.Uid 1)) (V.Int 0)
  , check (M.ScoreIs 0) (M.Is (V.Uid 0)) (V.Int 0)
  , check (M.ScoreIs 3) (M.Is (V.Uid 0)) (V.Int 14)
  , check (M.ScoreIs 3) (M.Is (V.Uid 0)) (V.Int 13)
  , check (M.ScoreIs 2) (M.Is (V.Uid 0)) (V.Int 12)
  , check M.ScoreNone (M.Is (V.Uid 0)) (V.Int 15)
  ])
  where
    check expected guard value = TestCase (assertEqual "" expected result)
      where
        result = M.matchGuard TestHierarchy guard value

maybeMap f (Just v) = Just (f v)
maybeMap _ Nothing = Nothing

sAn = M.ScoreAny
sEq = M.ScoreEq

testSignatureMatching = TestLabel "signatureMatching" (TestList
  [ check Nothing [([1], M.Any), ([2], M.Any)] [(1, 3)]
  , check Nothing [([1], M.Any), ([2], M.Any)] [(2, 3)]
  , check Nothing [([1], M.Any), ([2], M.Any)] [(3, 3)]
  , check (Just [(1, sAn)]) [([1], M.Any)] [(1, 3)]
  , check (Just [(1, sAn)]) [([1], M.Any)] [(1, 3), (2, 4)]
  , check (Just [(1, sAn)]) [([1], M.Any)] [(2, 5), (1, 6)]
  , check (Just [(1, sEq)]) [([1], M.Eq (V.Int 3))] [(1, 3)]
  , check Nothing [([1], M.Eq (V.Int 4))] [(1, 3)]
  , check (Just [(1, sAn), (2, sAn), (3, sAn)])
      [([1], M.Any), ([2], M.Any), ([3], M.Any)]
      [(1, 7), (2, 7), (3, 7)]
  , check (Just [(1, sAn), (3, sAn)]) [([1, 2], M.Any), ([3, 4], M.Any)] [(1, 10), (3, 11)]
  , check (Just [(2, sAn), (3, sAn)]) [([1, 2], M.Any), ([3, 4], M.Any)] [(2, 12), (3, 13)]
  , check (Just [(1, sAn), (4, sAn)]) [([1, 2], M.Any), ([3, 4], M.Any)] [(1, 14), (4, 15)]
  , check (Just [(2, sAn), (4, sAn)]) [([1, 2], M.Any), ([3, 4], M.Any)] [(2, 16), (4, 17)]
  ])
  where
    check expList sigList invList = TestCase (assertEqual "" expected result)
      where
        signature = [M.Parameter (map V.Int tags) guard | (tags, guard) <- sigList]
        invocation = Map.fromList [(V.Int key, V.Int value) | (key, value) <- invList]
        result = M.matchSignature TestHierarchy signature invocation
        expected = maybeMap wrapExpected expList
        wrapExpected scores = [(V.Int tag, score) | (tag, score) <- scores]

testAll = runTestTT (TestList
  [ testTokenize
  , testSexpParsing
  , testAstParsing
  , testUidStream
  , testEvalExpr
  , testMatchOrder
  , testSingleGuards
  , testSignatureMatching
  ])

main = testAll
