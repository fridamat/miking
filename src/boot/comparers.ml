open Ast
open Okasakiqueue
open Linkedlist

let compare_tm_terms tm1 tm2 =
  match tm1, tm2 with
  | TmConst(_,CInt(n1)), TmConst(_,CInt(n2)) -> (n1 = n2)
  | _ -> false

let rec compare_int_lists l1 l2 =
  match l1, l2 with
  | [], [] -> true
  | hd1::tl1, hd2::tl2 ->
    if compare_tm_terms hd1 hd2 then
      compare_int_lists tl1 tl2
    else
      false
  | _ -> failwith "We expected lists."

let compare_lists l1 l2 =
  match l1, l2 with
  | hd1::_, hd2::_ ->
    (
      match hd1, hd2 with
      | TmConst(_,CInt(_)), TmConst(_,CInt(_)) ->
        compare_int_lists l1 l2
      | _ -> failwith "Lists of this type is not allowed."
    )
  | _ -> failwith "We expected two lists."

let compare_tm_lists tm_l1 tm_l2 =
  match tm_l1, tm_l2 with
  | TmList(l1), TmList(l2) ->
    compare_lists l1 l2

let rec compare_term_lists l1 l2 =
let compare_sequences seq1 seq2 =
  (let (l1,l2) =
     (match seq1, seq2 with
      | SeqList(ll1), SeqList(ll2) ->
        ((Okasakiqueue.to_list ll1), (Okasakiqueue.to_list ll2))
      | SeqNone, SeqNone ->
        ([], [])
      | _ -> failwith "Comparison of sequence type not implemented.") in
   compare_term_lists l1 l2) in
  let rec compare_terms t1 t2 =
    (match t1, t2 with
     | TmChar(_,n1),TmChar(_,n2) -> n1 = n2
     | TmConst(_,c1),TmConst(_,c2) -> c1 = c2
     | TmNop, TmNop -> true
     | TmVar(_,id1,_,_), TmVar(_,id2,_,_) -> id1 = id2
     | TmLam(_,var1,ty1,tm1), TmLam(_,var2,ty2,tm2) ->
       (var1=var2) && (ty1=ty2) && (compare_terms tm1 tm2)
     | TmClos(_,var1,ty1,tm1,_,_), TmClos(_,var2,ty2,tm2,_,_) ->
       (var1=var2) && (ty1=ty2) && (compare_terms tm1 tm2)
     | TmApp(_,tm11,tm12), TmApp(_,tm21,tm22) ->
       (compare_terms tm11 tm21) && (compare_terms tm12 tm22)
     | TmIfexp(_,tm11,tm12,tm13), TmIfexp(_,tm21,tm22,tm23) ->
       (compare_terms tm11 tm21) && (compare_terms tm12 tm22) && (compare_terms tm13 tm23)
     | TmFix _, TmFix _ -> true
     | TmSeq(_,_,tm_l1,seq1,ds_choice1), TmSeq(_,_,tm_l2,seq2,ds_choice2) ->
       (compare_term_lists (get_list_from_tmlist tm_l1) (get_list_from_tmlist tm_l2)) && (compare_sequences seq1 seq2)
     | TmSeqMethod(_,fun_name1,_,_,_,_,_), TmSeqMethod(_,fun_name2,_,_,_,_,_) ->
       fun_name1 = fun_name2
     | _ -> false) in
  match l1, l2 with
  | [], [] -> true
  | hd1::tl1, hd2::tl2 ->
    if compare_terms hd1 hd2 then
      compare_term_lists tl1 tl2
    else
      false
  | _ -> false

let rec split_pair_list l lhs_l rhs_l=
  match l with
  | [] -> (lhs_l,rhs_l)
  | (hd1,hd2)::tl ->
    let lhs_l' = hd1::lhs_l in
    let rhs_l' = hd2::rhs_l in
    split_pair_list tl lhs_l' rhs_l'

let compare_term_pair_lists l1 l2 =
  let (l11,l12) = split_pair_list l1 [] [] in
  let (l21,l22) = split_pair_list l2 [] [] in
  (compare_term_lists l11 l21) && (compare_term_lists l12 l22)
