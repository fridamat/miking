let get_exp_args_length fun_name =
  match Ustring.to_utf8 fun_name with
  | "is_empty" -> 1
  | "first" -> 1
  | "last" -> 1
  | "push" -> 2
  | "pop" -> 1
  | "length" -> 1
  | "nth" -> 2
  | "append" -> 2
  | "reverse" -> 1
  | "push_last" -> 2
  | "pop_last" -> 1
  | "take" -> 2
  | "drop" -> 2
  | "map" -> 2
  | "any" -> 2
  | "seqall" -> 2
  | "find" -> 2
  | "filter" -> 2
  | "foldr" -> 3
  | "foldl" -> 3
  | "copy" -> 1
  | _ -> failwith "Sequence function not implemented"

let get_mc =
  [[Complexities.Const; (*Ocamlqueue: is_empty*)
    Complexities.Const; (*Ocamlqueue: first*)
    Complexities.X1; (*Ocamlqueue: last*)
    Complexities.Const; (*Ocamlqueue: push*)
    Complexities.Const; (*Ocamlqueue: pop*)
    Complexities.X1; (*Ocamlqueue: length*)
    Complexities.X1; (*Ocamlqueue: nth*)
    Complexities.X1; (*Ocamlqueue: append*)
    Complexities.X1; (*Ocamlqueue: reverse*)
    Complexities.X1; (*Ocamlqueue: push_last*)
    Complexities.X1; (*Ocamlqueue: pop_last*)
    Complexities.X1; (*Ocamlqueue: take*)
    Complexities.X1; (*Ocamlqueue: drop*)
    Complexities.X1; (*Ocamlqueue: map*)
    Complexities.X1; (*Ocamlqueue: any*)
    Complexities.X1; (*Ocamlqueue: seqall*)
    Complexities.X1; (*Ocamlqueue: find*)
    Complexities.X1; (*Ocamlqueue: filter*)
    Complexities.X1; (*Ocamlqueue: foldr*)
    Complexities.X1; (*Ocamlqueue: foldl*)
    Complexities.X1; (*Ocamlqueue: copy*)];]

let get_seq_fun_names =
  ["is_empty";
   "first";
   "last";
   "push";
   "pop";
   "length";
   "nth";
   "append";
   "reverse";
   "push_last";
   "pop_last";
   "take";
   "drop";
   "map";
   "any";
   "seqall";
   "find";
   "filter";
   "foldr";
   "foldl";
   "copy";]
