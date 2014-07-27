CM.make "$smlnj-tdp/back-trace.cm";
SMLofNJ.Internals.TDP.mode := true;

use "neutrino.sml";

(* Simple assertion library. Why does SML not come with something like this (or
   if it does, why couldn't I find it?). *)
structure Test = struct

  (* Error thrown on failed assertions. *)
  exception AssertionError;

  (* Fails unless the argument is true. *)
  fun assert_true true = ()
    | assert_true _ = raise AssertionError
  ;

  (* Fails unless the argument is false. *)
  fun assert_false false = ()
    | assert_false _ = raise AssertionError
  ;

  fun assert_equals a b = assert_true (a = b);

end;

(* Unit tests of the neutrino spec. *)
structure UnitTests = struct

  (* Abbreviations for modules. *)
  structure G = Guard;
  structure Sc = Score;
  structure Tt = Test;
  structure Tn = Token;
  structure V = Value;
  structure Sg = Signature;
  structure Sx = Sexp;
  structure P = Parser;
  structure E = Eval;

  (* Shorthands visible to all tests. *)
  val Int = V.Integer;
  val Null = V.Null;
  val Obj = V.Object;
  val Score = Sc.Score;
  val Str = V.String;
  val Uid = V.Uid;

  val scEq = Sc.scEq;
  val scIs = Sc.scIs;

  val any = G.any
  val assert_equals = Tt.assert_equals;
  val assert_false = Tt.assert_false;
  val assert_true = Tt.assert_true;
  val eq = G.eq
  val genuid = V.genuid;

  (* Test that the value identity stream works sensibly. *)
  fun test_id_factory () =
    let
      val s0 = V.uid_stream_start
      val (i0, s1) = genuid s0
      val (i1, s2) = genuid s1
      val (i2, s3) = genuid s2
    in
      assert_true (i0 = i0);
      assert_false (i0 = i1);
      assert_false (i0 = i2);
      assert_false (i1 = i0);
      assert_true (i1 = i1);
      assert_false (i1 = i2);
      assert_false (i2 = i0);
      assert_false (i2 = i1);
      assert_true (i2 = i2);
      ()
    end;

  (* Test value equality. *)
  fun test_value_eq () =
    let
      val == = V.==
      val s0 = V.uid_stream_start
      val (i0, s1) = genuid s0
      val o0 = Obj i0
      val (i1, s2) = genuid s1
      val o1 = Obj i1
    in 
      assert_true (== (Int 9) (Int 9));
      assert_false (== (Int 10) (Int 11));
      assert_true (== (Str "a") (Str "a"));
      assert_false (== (Str "a") (Str "b"));
      assert_false (== (Int 9) (Str "9"));
      assert_true (== o0 o0);
      assert_false (== o1 o0);
      assert_false (== o1 (Int 9));
      ()
    end;

  fun test_value_less () =
    let
      val less = V.less
    in
      assert_true (less (Int 8) (Int 9));
      assert_false (less (Int 10) (Int 10));
      assert_false (less (Int 12) (Int 11));
      assert_true (less (Str "a") (Str "b"));
      assert_false (less (Str "c") (Str "c"));
      assert_false (less (Str "e") (Str "d"));
      assert_true (less (Int 8) (Str ""));
      assert_true (less (Str "abc") Null);
      ()
    end;

  (* Test score comparison. *)
  fun test_is_score_better () =
    let
      fun is_better a b = Sc.is_score_better (Score a) (Score b)
    in
      assert_true (is_better (scEq, 1) (scEq, 0));
      assert_false (is_better (scEq, 0) (scEq, 1));
      assert_true (is_better (scIs, 1) (scIs, 0));
      assert_false (is_better (scIs, 0) (scIs, 1));

      assert_false (is_better (scIs, 1) (scEq, 0));
      assert_false (is_better (scIs, 0) (scEq, 1));
      assert_true (is_better (scEq, 1) (scIs, 0));
      assert_true (is_better (scEq, 0) (scIs, 1));      
      ()
    end;

  (* Simple test of equality guards. *)
  fun test_eq_guard () =
    let
      val match = G.match
      val eq_zero = eq (Int 0)
      val eq_null = eq Null
    in
      assert_equals (Sc.equal) (match eq_zero (Int 0));
      assert_equals (Sc.none) (match eq_zero Null);
      assert_equals (Sc.none) (match eq_null (Int 0));
      assert_equals (Sc.equal) (match eq_null Null);
      ()
    end;

  (* Simple test of any-guards. *)
  fun test_any_guard () =
    let
      val match = G.match
    in
      assert_equals (Sc.any) (match any (Int 0));
      assert_equals (Sc.any) (match any (Str "a"));
      assert_equals (Sc.any) (match any Null);
      ()
    end;

  fun test_match_argument () =
    let 
      fun check_match scores sign args
        = assert_equals
            (SOME scores) 
            (Sg.match (Sg.Signature sign) (Sg.Invocation args))
      fun check_no_match sign args
        = assert_equals
            NONE
            (Sg.match (Sg.Signature sign) (Sg.Invocation args))
    in
      check_match
        [(Int 0, Sc.any), (Int 1, Sc.any)]
        [(Int 0, any), (Int 1, any)]
        [(Int 0, Null), (Int 1, Null)];
      check_match
        [(Int 0, Sc.equal), (Int 1, Sc.equal)]
        [(Int 0, eq (Str "x")), (Int 1, eq (Str "y"))]
        [(Int 0, Str "x"), (Int 1, Str "y")];      
      check_match
        [(Int 0, Sc.equal), (Int 1, Sc.equal)]
        [(Int 1, eq (Str "x")), (Int 0, eq (Str "y"))]
        [(Int 0, Str "y"), (Int 1, Str "x")];      
      check_no_match
        [(Int 0, any)]
        [(Int 1, Null)];
      ()
    end;

  fun test_tokenize () =
    let
      val Dm = Tn.Delimiter;
      val Id = Tn.Ident;
      val It = Tn.Integer;
      val Op = Tn.Operation;
      val Wd = Tn.Word;
      fun check_tokens expected input =
        assert_equals expected (Tn.tokenize input)
    in
      check_tokens [Id "foo"] "$foo";
      check_tokens [Op "foo"] " .foo ";
      check_tokens [Op "<+>"] " <+> ";
      check_tokens [Dm ":="] " := ";
      check_tokens [Wd "foo"] " foo ";
      check_tokens [It 3] " 3 ";
      check_tokens [Id "foo", Id "bar", Id "baz"] "$foo$bar$baz";
      check_tokens [Id "foo", Id "bar", Id "baz"] "$foo $bar $baz";
      check_tokens [Id "foo"] "$foo";
      check_tokens [Dm "(", Id "foo", Dm ")"] "($foo)";
      ()
    end;

  fun test_sexp_parsing () =
    let
      val W = Sx.Word;
      val I = Sx.Ident;
      val L = Sx.List;
      fun check_parse expected input =
        assert_equals expected (Sx.parse input)
    in
      check_parse (W "foo") "foo";
      check_parse (I "foo") "$foo";
      check_parse (Sx.Integer 10) "10";
      check_parse (L []) "()";
      check_parse (L [(W "foo")]) "(foo)";
      check_parse (L [(W "foo"), (W "bar")]) "(foo bar)";
      check_parse (L [(W "foo"), (W "bar"), (W "baz")]) "(foo bar baz)";
      check_parse (L [L [L []]]) "((()))";
      ()
    end;

  fun test_full_parsing () =
    let
      val Var = V.Variable;
      val Seq = V.Sequence;
      val WEs = V.WithEscape;
      val Lit = V.Literal;
      val Def = V.LocalBinding;
      fun check_parse expected input =
        assert_equals expected (P.parse input)
    in
      check_parse (Var (Str "foo")) "$foo";
      check_parse (Lit (Int 10)) "10";
      check_parse (WEs (Str "s", Var (Str "t"))) "(with_escape $s do $t)";
      check_parse (Seq [Var (Str "a"), Var (Str "b")]) "(begin $a $b)";
      check_parse (Seq [Var (Str "a")]) "(begin $a)";
      check_parse (Lit Null) "(begin)";
      check_parse (Def (Str "a", Lit (Int 3), Var (Str "a"))) "(def $a := 3 in $a)";
      ()
    end;

  fun test_eval () =
    let
      fun check_eval expected_result expected_log input =
        let
          val (E.Success result, p0) = (E.eval (P.parse input))
          val log = (#log p0)
        in
          assert_equals expected_result result;
          assert_equals expected_log log;
          ()
        end
      fun check_fail expected_cause expected_log input =
        let
          val (E.Abort cause, p0) = (E.eval (P.parse input))
          val log = (#log p0)
        in
          assert_equals expected_cause cause;
          assert_equals expected_log log;
          ()
        end
    in
      check_eval Null [] "(begin)";
      check_eval Null [] "null";
      check_eval (Int 3) [] "3";
      check_eval (Int 4) [] "(begin 2 3 4)";
      check_eval (Int 8) [] "(def $a := 8 in $a)";
      check_eval (Int 9) [] "(def $a := 9 in (def $b := 10 in $a))";
      check_eval (Int 12) [] "(def $a := 11 in (def $b := 12 in $b))";
      check_eval (Obj (Uid 0)) [] "(new)";
      check_eval (Obj (Uid 1)) [] "(begin (new) (new))";
      check_eval (Obj (Uid 0)) [] "(def $x := (new) in $x)";
      check_eval (Int 3) [Int 3] "(log 3)";
      check_eval (Int 7) [Int 5, Int 6, Int 7] "(begin (log 5) (log 6) (log 7))";
      check_eval (Int 5) [] "(with_escape $e do (call $e 5))";
      check_eval (Int 6) [] "(with_escape $e do (log (call $e 6)))";
      check_eval (Int 7) [Int 1] "(with_escape $e do (begin (log 1) (call $e 7) (log 2)))))";
      check_fail (E.UnresolvedVariable (Str "b")) [] "(def $a := 8 in $b)";
      check_fail (E.UnresolvedVariable (Str "c")) [Int 1] "(def $a := 8 in (begin (log 1) $c (log 2)))";
      ()
    end;

  fun test_field_eval () =
    let
      fun check_eval expected input =
        let
          val code = "(def $f := (new_field) in (def $o := (new) in " ^ input ^ "))"
          val (result, p0) = (E.eval (P.parse code))
          val log = (#log p0)
        in
          assert_equals expected log
        end
    in
      check_eval [Null] "(log (get $f $o))";
      check_eval [Null, Int 3, Int 3] "(begin (log (get $f $o)) (log (set $f $o 3)) (log (get $f $o)))";
      ()
    end;

  fun test_ensure () =
    let
      fun check_ensure expected input =
        let
          val (result, p0) = (E.eval (P.parse input))
          val log = (#log p0)
        in
          assert_equals expected log
        end
    in
      check_ensure [Int 4, Int 5, Int 4] "(log (after (log 4) ensure (log 5)))";
      check_ensure [Int 6, Int 7, Int 9] (
        "(with_escape $e do " ^
          "(begin" ^ 
            "(log 6)" ^
              "(after (begin" ^
                "(log 7)" ^
                "(call $e 5)" ^
                "(log 8))" ^
              " ensure (log 9))))");
      ()
    end;

  (* Remember to add new test functions to this one. *)
  fun test_all () =
    let
      fun run_test test name = (
        print (" - Running " ^ name ^ "\n");
        test ()
      )
    in
      print "--- Running all tests ---\n";
      run_test test_id_factory "test_id_factory";
      run_test test_value_eq "test_value_eq";
      run_test test_value_less "test_value_less";
      run_test test_is_score_better "test_is_score_better";
      run_test test_eq_guard "test_eq_guard";
      run_test test_any_guard "test_any_buard";
      run_test test_match_argument "test_match_argument";
      run_test test_tokenize "test_tokenize";
      run_test test_sexp_parsing "test_sexp_parsing";
      run_test test_full_parsing "test_full_parsing";
      run_test test_eval "test_eval";
      run_test test_field_eval "test_field_eval";
      run_test test_ensure "test_ensure";
      ()
    end;

end;

(* Run *all* the tests. *)
BackTrace.monitor (fn () => UnitTests.test_all ());

(* Exit explicitly otherwise the interpreter will hang. *)
val _ = OS.Process.exit(OS.Process.success);
