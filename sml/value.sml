(* Stuff related to runtime values *)
structure Value = struct

  (* Encapsulated value identity. *)
  datatype uid
    = Uid of int;

  (* A stream of value identities. *)
  datatype uid_stream
    = UidStream of int;

  (* An id stream starting from id 0. *)
  val uid_stream_start = UidStream 0;

  (* Given an id stream, returns the next id which will be distinct from all
     ids previously returned, as well as a new identity stream which will
     produce a stream of identities distinct from any previously returned. *)
  fun genuid (UidStream next_uid) = (Uid next_uid, UidStream (next_uid + 1));

  (* A runtime value. *)
  datatype value
    = Integer of int
    | String of string
    | Object of uid
    | Field of uid
    | Type of uid
    | Null
    | Thunk of value list * ast

  (* Kernel language syntax. Some of these are surface-level, some are synthetic
     for instance FireEscape which you can't write in the syntax but which
     get created during evaluation. *)
  and ast
    = Literal of value
    | Variable of value
    | Sequence of ast list
    | LocalBinding of value * ast * ast
    | NewObject
    (* Escape *)
    | WithEscape of value * ast
    | FireEscape of uid * ast
    | Ensure of ast * ast
    (* Fields *)
    | NewField
    | SetField of ast * ast * ast
    | GetField of ast * ast
    (* Debug/test *)
    | Log of ast
    | CallThunk of ast * ast
  ;

  datatype value_mode
    = Fluid
    | Mutable
    | Frozen
  ;

  (* The mutable data backing an object. *)
  type object_state = {
    mode: value_mode,
    fields: (uid, value) Dict.dict
  };

  fun set_object_state_field state uid value =
    let
      val {mode=m, fields=fields} = state
      val new_fields = Dict.set fields uid value
    in
      {mode=m, fields=new_fields}
    end;

  (* The initial state of a fresh object. *)
  val empty_object_state : object_state = {
    mode = Fluid,
    fields = Dict.empty
  };

  (* Defines the ordering between values of different types. *)
  fun value_ordinal (Integer _) = 0
    | value_ordinal (String _) = 1
    | value_ordinal (Object _) = 2
    | value_ordinal (Type _) = 3
    | value_ordinal Null = 4
  ;

  (* Given two values, returns true iff they are equal. *)
  fun op == (Integer a) (Integer b) = (a = b)
    | op == (String a) (String b) = (a = b)
    | op == (Object a) (Object b) = (a = b)
    | op == (Type a) (Type b) = (a = b)
    | op == Null Null = true
    | op == _ _ = false
  ;

  exception NotComparable;

  (* Returns true iff the first argument is less than the second. *)
  fun less (Integer a) (Integer b) = (a < b)
    | less (String a) (String b) = (a < b)
    | less Null Null = false
    | less a b =
      let
        val oa = value_ordinal a
        val ob = value_ordinal b
      in
        if oa = ob
          (* Only the types listed in the previous clauses are comparable within
             their categories so this must one that isn't. *)
          then raise NotComparable
          else oa < ob
      end;
end;
