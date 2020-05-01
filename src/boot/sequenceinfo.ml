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
  [[Complexities.Const; (*Ocamlarray: is_empty*)
    Complexities.Const; (*Ocamlarray: first*)
    Complexities.X1; (*Ocamlarray: last*)
    Complexities.Const; (*Ocamlarray: push*)
    Complexities.Const; (*Ocamlarray: pop*)
    Complexities.X1; (*Ocamlarray: length*)
    Complexities.X1; (*Ocamlarray: nth*)
    Complexities.X1; (*Ocamlarray: append*)
    Complexities.X1; (*Ocamlarray: reverse*)
    Complexities.X1; (*Ocamlarray: push_last*)
    Complexities.X1; (*Ocamlarray: pop_last*)
    Complexities.X1; (*Ocamlarray: take*)
    Complexities.X1; (*Ocamlarray: drop*)
    Complexities.X1; (*Ocamlarray: map*)
    Complexities.X1; (*Ocamlarray: any*)
    Complexities.X1; (*Ocamlarray: seqall*)
    Complexities.X1; (*Ocamlarray: find*)
    Complexities.X1; (*Ocamlarray: filter*)
    Complexities.X1; (*Ocamlarray: foldr*)
    Complexities.X1; (*Ocamlarray: foldl*)
    Complexities.X1; (*Ocamlarray: copy*)];]

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
