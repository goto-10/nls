use "utils.sml";
use "value.sml";

(* Stuff related to working with individual scores. *)
structure Score = struct

  (* Scores are grouped into categories. Two scores in different categories
     are compared based just on the category, only scores within the same
     category use the score value. *)
  datatype score_category
    = scEq
    | scIs
    | scAny
    | scExtra
    | scNone
  ;

  (* Given a category, returns an integer signifying where it ranks in the order
     of categories. *)
  fun score_category_ordinal sc =
    case sc
      of scEq => 0
       | scIs => 1
       | scAny => 2
       | scExtra => 3
       | scNone => 4
  ;

  (* Returns true iff a score with category a is considered better than a score
     in category b. *)
  fun is_score_category_better a b 
    = (score_category_ordinal a) < (score_category_ordinal b);

  (* A score from matching a value against a guard. *)
  datatype score
    = Score of score_category * int
  ;

  (* Is the first score considered better than the second? *)
  fun is_score_better (Score (c1, v1)) (Score (c2, v2)) =
    (is_score_category_better c1 c2) orelse (c1 = c2 andalso v1 > v2);

  (* A score that signifies that matching failed. *)
  val none = Score (scNone, 0);

  (* Score that signifes that an any-guard matched. *)
  val any = Score (scAny, 0);

  (* Score that signifies that an eq-guard matched. *)
  val equal = Score (scEq, 0);

end;


(* Stuff related to working with guards. *)
structure Guard = struct

  (* A parameter guard *)
  datatype guard
    = gEq of Value.value
    | gIs of Value.uid
    | gAny
  ;

  (* Matches a guard against a value, returning the value's score. *)
  fun match guard value =
    let
      fun match_eq a b =
        if Value.== a b
          then Score.equal
          else Score.none
      fun match_is t v =
        Score.none
    in
      case guard
        of (gEq v) => match_eq v value
         | (gIs t) => match_is t value
         | gAny => Score.any
    end;

  (* Guard that matches anything. *)
  val any = gAny;

  (* Returns a guard that eq-matches the given value. *)
  fun eq v = gEq v;

end;


structure Signature = struct

  (* A signature (deliberately misspelled because 'signature' is reserved).
     The order of parameters is not significant. *)
  datatype signaturr
    = Signature of (Value.value * Guard.guard) list
  ;

  (* A full invocation. The order of arguments is not significant. *)
  datatype invocation
    = Invocation of (Value.value * Value.value) list
  ;

  (* Match a single argument against a signature, returning an option that gives
     either the score or NONE if there is no corresponding parameter. *)
  fun match_argument sign (tag, value) =
    let
      (* Look for the matching parameter *)
      fun is_the_param (t, _) = (t = tag);
      val param = (List.find is_the_param sign);
      (* Function that maps a parameter to its score. *)
      fun score_param (_, g) = (tag, Guard.match g value);
    in
      Option.map score_param param
    end;

  exception Unrechable;

  (* Given a list of options, returns either SOME of a list of all the option
     values if they're all SOME, or NONE if any element is NONE. *)
  fun list_all_or_nothing elms =
    let
      (* Is the argument NONE? *)
      fun is_none NONE = true
        | is_none _ = false
      (* Gives the value of a SOME option, fails on NONE. *)
      fun get_some (SOME v) = v
        | get_some _ = raise Unrechable
      val has_none = List.exists is_none elms
    in
      if has_none
        then NONE
        else SOME (map get_some elms)
    end;

  (* Match a full signature against a full invocation. *)
  fun match (Signature params) (Invocation args) =
    let
      (* The raw list of scores possibly containing NONEs *)
      val raw_scores = map (match_argument params) args
    in
      (* Elevate the options from the individual args to the whole result. *)
      list_all_or_nothing raw_scores
    end

end;

use "eval.sml";
use "syntax.sml";
