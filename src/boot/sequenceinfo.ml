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
  [[Complexities.Const; (*Ocamlstack: is_empty*)
    Complexities.Const; (*Ocamlstack: first*)
    Complexities.X1; (*Ocamlstack: last*)
    Complexities.Const; (*Ocamlstack: push*)
    Complexities.Const; (*Ocamlstack: pop*)
    Complexities.X1; (*Ocamlstack: length*)
    Complexities.X1; (*Ocamlstack: nth*)
    Complexities.X1; (*Ocamlstack: append*)
    Complexities.X1; (*Ocamlstack: reverse*)
    Complexities.X1; (*Ocamlstack: push_last*)
    Complexities.X1; (*Ocamlstack: pop_last*)
    Complexities.X1; (*Ocamlstack: take*)
    Complexities.X1; (*Ocamlstack: drop*)
    Complexities.X1; (*Ocamlstack: map*)
    Complexities.X1; (*Ocamlstack: any*)
    Complexities.X1; (*Ocamlstack: seqall*)
    Complexities.X1; (*Ocamlstack: find*)
    Complexities.X1; (*Ocamlstack: filter*)
    Complexities.X1; (*Ocamlstack: foldr*)
    Complexities.X1; (*Ocamlstack: foldl*)
    Complexities.X1; (*Ocamlstack: copy*)];]

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
