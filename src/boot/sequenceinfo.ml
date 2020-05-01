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
  [[Complexities.Const; (*Linkedlist: is_empty*)
    Complexities.Const; (*Linkedlist: first*)
    Complexities.X1; (*Linkedlist: last*)
    Complexities.Const; (*Linkedlist: push*)
    Complexities.Const; (*Linkedlist: pop*)
    Complexities.X1; (*Linkedlist: length*)
    Complexities.X1; (*Linkedlist: nth*)
    Complexities.X1; (*Linkedlist: append*)
    Complexities.X1; (*Linkedlist: reverse*)
    Complexities.X1; (*Linkedlist: push_last*)
    Complexities.X1; (*Linkedlist: pop_last*)
    Complexities.X1; (*Linkedlist: take*)
    Complexities.X1; (*Linkedlist: drop*)
    Complexities.X1; (*Linkedlist: map*)
    Complexities.X1; (*Linkedlist: any*)
    Complexities.X1; (*Linkedlist: seqall*)
    Complexities.X1; (*Linkedlist: find*)
    Complexities.X1; (*Linkedlist: filter*)
    Complexities.X1; (*Linkedlist: foldr*)
    Complexities.X1; (*Linkedlist: foldl*)
    Complexities.X1; (*Linkedlist: copy*)];]

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
