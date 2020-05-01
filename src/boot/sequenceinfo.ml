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
    Complexities.X1; (*Linkedlist: copy*)];
   [Complexities.Const; (*Okasakiqueue: is_empty*)
    Complexities.Const; (*Okasakiqueue: first*)
    Complexities.X1; (*Okasakiqueue: last*)
    Complexities.Const; (*Okasakiqueue: push*)
    Complexities.X1; (*Okasakiqueue: pop*)
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
    Complexities.X1; (*Okasakiqueue: copy*)];
   [Complexities.Const; (*Ocamlarray: is_empty*)
    Complexities.Const; (*Ocamlarray: first*)
    Complexities.Const; (*Ocamlarray: last*)
    Complexities.X1; (*Ocamlarray: push*)
    Complexities.X1; (*Ocamlarray: pop*)
    Complexities.Const; (*Ocamlarray: length*)
    Complexities.Const; (*Ocamlarray: nth*)
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
    Complexities.X2; (*Ocamlarray: filter*)
    Complexities.X1; (*Ocamlarray: foldr*)
    Complexities.X1; (*Ocamlarray: foldl*)
    Complexities.X1; (*Ocamlarray: copy*)];
   [Complexities.Const; (*Ocamlqueue: is_empty*)
    Complexities.X1; (*Ocamlqueue: first*)
    Complexities.X1; (*Ocamlqueue: last*)
    Complexities.X1; (*Ocamlqueue: push*)
    Complexities.X1; (*Ocamlqueue: pop*)
    Complexities.Const; (*Ocamlqueue: length*)
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
    Complexities.X1; (*Ocamlqueue: copy*)];
   [Complexities.Const; (*Ocamlstack: is_empty*)
    Complexities.X1; (*Ocamlstack: first*)
    Complexities.X1; (*Ocamlstack: last*)
    Complexities.X1; (*Ocamlstack: push*)
    Complexities.X1; (*Ocamlstack: pop*)
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
    Complexities.X1; (*Ocamlstack: copy*)];
    [Complexities.Const; (*Fingertree: is_empty*)
     Complexities.X1; (*Fingertree: first*)
     Complexities.X1; (*Fingertree: last*)
     Complexities.X1; (*Fingertree: push*)
     Complexities.X1; (*Fingertree: pop*)
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
