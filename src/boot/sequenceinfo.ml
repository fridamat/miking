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
  [[Complexities.Const; (*Fingertree: is_empty*)
    Complexities.Const; (*Fingertree: first*)
    Complexities.X1; (*Fingertree: last*)
    Complexities.Const; (*Fingertree: push*)
    Complexities.Const; (*Fingertree: pop*)
    Complexities.X1; (*Fingertree: length*)
    Complexities.X1; (*Fingertree: nth*)
    Complexities.X1; (*Fingertree: append*)
    Complexities.X1; (*Fingertree: reverse*)
    Complexities.X1; (*Fingertree: push_last*)
    Complexities.X1; (*Fingertree: pop_last*)
    Complexities.X1; (*Fingertree: take*)
    Complexities.X1; (*Fingertree: drop*)
    Complexities.X1; (*Fingertree: map*)
    Complexities.X1; (*Fingertree: any*)
    Complexities.X1; (*Fingertree: seqall*)
    Complexities.X1; (*Fingertree: find*)
    Complexities.X1; (*Fingertree: filter*)
    Complexities.X1; (*Fingertree: foldr*)
    Complexities.X1; (*Fingertree: foldl*)
    Complexities.X1; (*Fingertree: copy*)];]

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
