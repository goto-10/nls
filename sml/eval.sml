structure Ast = struct

  datatype path
    = Path of string list
  ;

  (* Kernel language syntax. Some of these are surface-level, some are synthetic
     for instance FireEscape which you can't write in the syntax but which
     get created during evaluation. *)
  datatype ast
    = Literal of Value.value
    | WithEscape of string * ast
    | FireEscape of int * ast
    | Variable of string
    | Sequence of ast list
    | LocalBinding of string * ast * ast
  ;

end;

structure Eval = struct

  (* The id of the destination of a non-local escape. *)
  type non_local_id = int;

  (* The ambient, non-scoped, state. This flows linearly through the evaluation
     independent of scope and control flow -- for instance, leaving a scope can
     restore a previous scope state but nothing can restore a previous ambient
     state. *)
  type ambient_state = {
    (* The next object id. *)
    next_id: non_local_id
  };

  (* A local continuation, the next step during normal evaluation. Continuations
     always continue in the scope they captured when they were created whereas
     the ambient state is always passed in. *)
  type continuation = Value.value -> ambient_state -> Value.value;

  (* A non-local continuation, the next step in performing a non-local escape.
     The id identifies the destination we're trying to escape to, the rest is
     the continuation to return to once the destination has been found. *)
  type non_local_continuation = non_local_id -> continuation;

  (* Scoped state. Leaving a scope implicitly restores outer scope state. *)
  type scope_state = {
    (* The currently active non-local continuation. *)
    non_local: non_local_continuation,
    (* The current variable resolution function. *)
    lookup_variable: string -> Value.value option
  };

  (* This should probably raise an exception actually, escaping to somewhere
     that doesn't exist. *)
  fun toplevel_non_local_continuation target_id value ambient =
    value;

  (* Toplevel variable lookup. *)
  fun toplevel_lookup_variable name = NONE;

  (* The initial scope descriptor that describes the toplevel scope. *)
  val toplevel_scope_state : scope_state = {
    non_local = toplevel_non_local_continuation,
    lookup_variable = toplevel_lookup_variable
  };

  (* The initial ambient state. *)
  val initial_ambient_state : ambient_state = {
    next_id = 0
  };

  (* Returns a new scope state with the given non_local continuation as the
     top non_local. *)
  fun set_non_local ({lookup_variable=lv, ...} : scope_state) value
    = {non_local=value, lookup_variable=lv};

  (* Returns a new scope state with the given lookup function as the variable
     resolver. *)
  fun set_lookup_variable ({non_local=nl, ...} : scope_state) value
    = {lookup_variable=value, non_local=nl};

  fun push_binding scope name value =
    let
      val outer = (#lookup_variable scope)
      fun lookup n =
        if (n = name)
          then (SOME value)
          else (outer n)
    in
      (set_lookup_variable scope lookup)
    end;

  (* Returns a new unique id pulled from the given ambient state as well as a
     new ambient state to use from here on. *)
  fun gen_id ({next_id=id, ...} : ambient_state) =
    (id, {next_id = id + 1});

  exception UnresolvedVariable of string;

  (* Executes a single evaluation step. *)
  fun step expr continue s0 a0 = 
    case expr
      of Ast.Literal value 
      => (continue value a0)
       | Ast.WithEscape (name, body)
      => step_with_escape name body continue s0 a0
       | Ast.FireEscape (target_id, body)
      => step_fire_escape target_id body s0 a0
       | Ast.Variable name
      => step_variable name continue s0 a0
       | Ast.Sequence exprs
      => step_sequence exprs continue s0 a0
       | Ast.LocalBinding (name, value, body)
      => step_local_binding name value body continue s0 a0

  and step_with_escape name body continue s0 a0 =
    let
      (* Acquire an ie for this escape. This'll be used to identify this as the
         destination for the escape thunk. *)
      val (escape_id, a1) = gen_id a0
      (* Grab the non_local that was in effect immediately before this
         expression. *)
      val outer_non_local = (#non_local s0)
      (* The new topmost non-local handler that will be in effect for the body. *)
      fun non_local_escape target_id value a2 =
        if (target_id = escape_id)
          (* If someone escapes non-locally with this escape as the target we
             simply continue on from immediately after this. *)
          then (continue value a2)
          (* If they're escaping to another target it must be outside this
             escape so we just let it keep going through the next outer
             nonlocal and discard this expression and its continuation. *)
          else (outer_non_local target_id value a2)
      val outer_lookup_variable = (#lookup_variable s0)
      (* Install the new non-local. *)
      val s1 = set_non_local s0 non_local_escape
      (* Create a binding for the symbol. *)
      val s2 = push_binding s1 name (Value.Integer 8)
    in
      (step body continue s2 a1)
    end

  and step_fire_escape target_id body s0 a0 =
    let
      (* This is the non-local continuation we'll eventually fire. *)
      val non_local = (#non_local s0)
      (* The local continuation to execute if the body completes normally. *)
      fun fire_escape value a1 =
        (non_local target_id value a1)
    in
      (step body fire_escape s0 a0)
    end

  and step_variable name continue s0 a0 =
    let
      val lookup = (#lookup_variable s0)
    in
      case lookup name
        of SOME value => (continue value a0)
         | NONE => raise (UnresolvedVariable name)
    end

  and step_sequence [only] continue s0 a0 =
      (* A sequence of one expression is equivalent to that one expression. *)
      (step only continue s0 a0)
    | step_sequence (next::rest) continue s0 a0 =
      (* First evaluate the first expression, discard the value, then evaluate
         the rest. *)
      let
        fun continue_rest _ a1 = (step_sequence rest continue s0 a1)
      in
        (step next continue_rest s0 a0)
      end

  and step_local_binding name value_expr body continue s0 a0 =
    let
      (* Continuation that is fired when the value has been evaluated. Binds the
         value to the binding's name and evaluates the body in that scope. *)
      fun continue_with_binding value a1 =
        let
          val s1 = push_binding s0 name value
        in
          step body continue s1 a1
        end
    in
      step value_expr continue_with_binding s0 a0
    end

  fun yield_value value ambient = value;

  fun eval expr = step expr yield_value toplevel_scope_state initial_ambient_state;

end;
