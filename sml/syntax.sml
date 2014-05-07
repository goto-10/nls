(* Parsing and lexical stuff. *)

(* Import the regex library for simple source parsing. *)
CM.make "$/regexp-lib.cm";

(* Regexp library binding we'll be using. *)
structure RE = RegExpFn(
  structure P = AwkSyntax
  structure E = BackTrackEngine)

(* Tokens and tokenization. *)
structure Token = struct

  datatype token
    = Ident of string
    | Operation of string
    | Integer of int
    | Word of string
    | Delimiter of string
    | Error of string
  ;

  (* Returns a string reader that reads the given string. *)
  fun reader str idx =
    if idx < (String.size str)
      then SOME (String.sub(str, idx), idx + 1)
      else NONE;

  (* Returns the contents of the group'th capture from the given match tree
     which was produced by matching against the given input. *)
  fun get_capture tree group input =
    let
      val {pos=p, len=l} = (MatchTree.nth (tree, group))
    in
      String.substring(input, p, l)
    end

  (* Identifiers *)
  val re_ident = RE.compileString "\\$([a-z_]+)";
  fun handle_ident tree input = [Ident (get_capture tree 1 input)]

  (* Named operations *)
  val re_named_operation = RE.compileString "\\.([a-z_]+)";
  fun handle_named_operation tree input = [Operation (get_capture tree 1 input)];

  (* Operator operations *)
  val re_operation = RE.compileString "[+<>=:]+";
  fun handle_operation tree input =
    let
      val str = get_capture tree 0 input
    in
      if (str = ":=")
        then [Delimiter str]
        else [Operation str]
    end;

  (* Integer literals *)
  val re_integer = RE.compileString "[0-9]+";
  fun handle_integer tree input =
    let
      val str = get_capture tree 0 input
    in
      case (Int.fromString str)
        of SOME i => [Integer i]
         | NONE => [Error str]
    end;

  (* Words *)
  val re_word = RE.compileString "[a-z_]+";
  fun handle_word tree input = [Word (get_capture tree 0 input)];

  (* Delimiters *)
  val re_delimiter = RE.compileString "[(){}]";
  fun handle_delimiter tree input = [Delimiter (get_capture tree 0 input)];

  (* Whitespace *)
  val re_space = RE.compileString "[ \t\f\n\r]";
  fun ignore_token tree input = []

  (* List of regexes and handlers in the order in which they should be tried. *)
  val re_all = [
    (re_ident, handle_ident),
    (re_named_operation, handle_named_operation),
    (re_integer, handle_integer),
    (re_operation, handle_operation),
    (re_word, handle_word),
    (re_delimiter, handle_delimiter),
    (re_space, ignore_token)
  ];

  (* Returns the next tokens from the input, starting from the given index. The
     result is a pair of the next index after the tokens and a list of the
     tokens. Only semantic tokens are returned -- whitespace is ignored for
     instance and causes an empty list to be returned. *) 
  fun match_next_token input idx =
    let
      val getc = reader input
      fun match_successive_regexes ((re, handler)::rest) =
        (* Try the next regex. If it succeeds we're done, otherwise move on
           to the next regex. *)
          (case (RE.prefix re getc idx)
            of SOME (tree, pos) => (pos, handler tree input)
             | NONE => match_successive_regexes rest)
        (* Tried 'em all, none worked. Return an error and move on to the next
           token. *)
        | match_successive_regexes [] =
          (idx + 1, [Error (String.substring (input, idx, 1))])
    in
      match_successive_regexes re_all
    end;

  (* Tokenizes the rest of the input starting from the given index. *)
  fun tokenize_from input idx =
    let
      val (next_idx, tokens) = (match_next_token input idx)
    in
      if next_idx < (String.size input)
        then tokens @ (tokenize_from input next_idx)
        else tokens
    end;

  fun tokenize input = tokenize_from input 0

end;

(* A generic s-expression parser that groups a stream of neutrino tokens such
   that they're easier to consume for the neutrino s-expression parser. *)
structure Sexp = struct

  structure T = Token;

  (* Neutrino-specific s-expressions. Unlike classical s-expressions these ones
     retain the distinctions between the different token types. *)
  datatype sexp
    = Word of string
    | Ident of string
    | Operation of string
    | Delimiter of string
    | Integer of int
    | List of sexp list
    | Error of T.token
  ;

  exception SyntaxError;

  (* Parse the next s-expression in the given stream, returning the result and
     the remaining stream that wasn't consumed. *)
  fun parse_sexp ((T.Word v)::r0) = (Word v, r0)
    | parse_sexp ((T.Ident i)::r0) = (Ident i, r0)
    | parse_sexp ((T.Integer i)::r0) = (Integer i, r0)
    | parse_sexp ((T.Operation n)::r0) = (Operation n, r0)
    | parse_sexp ((T.Delimiter "(")::r0) = parse_list r0 []
    | parse_sexp ((T.Delimiter ":=")::r0) = (Delimiter ":=", r0)
    | parse_sexp (t::rest) = (Error t, [])
    | parse_sexp [] = (Error (T.Error "eof"), [])

  (* Parse the given stream as the rest of a list of expressions. The second
     argument is a list accumulating expressions in reverse order. *)
  and parse_list ((T.Delimiter ")")::r0) exprs = (List (rev exprs), r0)
    | parse_list r0 exprs =
      let
        val (elm, r1) = parse_sexp r0
      in
        parse_list r1 (elm::exprs)
      end

  (* Parse the given string into an s-expression. *)
  fun parse input =
    let
      val (ast, rest) = parse_sexp (Token.tokenize input);
    in
      ast
    end;

end;

(* The neutrino s-expression parser. *)
structure Parser = struct

  structure S = Sexp;
  structure A = Ast;
  structure V = Value;

  exception ParseError of S.sexp;

  (* Parse the given generic s-expression as a neutrino s-expression. *)
  fun parse_expr (S.Integer i) = A.Literal (V.Integer i)
    | parse_expr (S.Ident n) = A.Variable n
    | parse_expr (S.List [S.Word "with_escape", S.Ident name, body]) =
      A.WithEscape (name, parse_expr body)
    | parse_expr (S.List ((S.Word "begin")::rest)) =
      (* Get rid of trivial sequences at this level so we can assume they have
         length at least one. *)
      (case (map parse_expr rest)
         of [] => A.Literal (V.Null)
          | more => A.Sequence more)
    | parse_expr (S.List [S.Word "def", S.Ident name, S.Delimiter ":=", value, S.Word "in", body]) =
      A.LocalBinding (name, parse_expr value, parse_expr body)
    | parse_expr sexp = raise (ParseError sexp)

  (* Parse the given string as a neutrino s-expression, returning a syntax tree. *)
  fun parse input = parse_expr (S.parse input);

end;
