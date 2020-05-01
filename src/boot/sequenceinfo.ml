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
  [[Complexities.Const; (*Okasakiqueue: is_empty*)
    Complexities.Const; (*Okasakiqueue: first*)
    Complexities.X1; (*Okasakiqueue: last*)
    Complexities.Const; (*Okasakiqueue: push*)
    Complexities.Const; (*Okasakiqueue: pop*)
    Complexities.X1; (*Okasakiqueue: length*)
    Complexities.X1; (*Okasakiqueue: nth*)
    Complexities.X1; (*Okasakiqueue: append*)
    Complexities.X1; (*Okasakiqueue: reverse*)
    Complexities.X1; (*Okasakiqueue: push_last*)
    Complexities.X1; (*Okasakiqueue: pop_last*)
    Complexities.X1; (*Okasakiqueue: take*)
    Complexities.X1; (*Okasakiqueue: drop*)
    Complexities.X1; (*Okasakiqueue: map*)
    Complexities.X1; (*Okasakiqueue: any*)
    Complexities.X1; (*Okasakiqueue: seqall*)
    Complexities.X1; (*Okasakiqueue: find*)
    Complexities.X1; (*Okasakiqueue: filter*)
    Complexities.X1; (*Okasakiqueue: foldr*)
    Complexities.X1; (*Okasakiqueue: foldl*)
    Complexities.X1; (*Okasakiqueue: copy*)];]

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
