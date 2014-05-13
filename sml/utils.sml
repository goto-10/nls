(* A simple stupid dictionary. Seriously, how can ML not ship with one of
   these?!? *)
structure Dict = struct

  type (''k, 'v) dict = (''k * 'v) list;

  val empty = [];

  (* Returns a new dictionary which is identical to the given one except that
     the given key is bound to the given value. *)
  fun set [] key value = [(key, value)]
    | set ((k, v)::rest) key value =
      if k = key
        then (key, value)::rest
        else [(k, v)] @ (set rest key value)
  ;

  (* Returns SOME of the binding for the given key if it is present in the
     given map, otherwise NONE. *)
  fun get [] _ = NONE
    | get ((k, v)::rest) key =
      if k = key
        then (SOME v)
        else (get rest key)
  ;

end;
