open Ast
open Typesys

(*Print methods*)
let rec get_tm_pair_list_string pl =
  match pl with
  | [] -> "\n"
  | (hd1,hd2)::tl ->
    "- " ^ (Ustring.to_utf8 (Pprint.pprint false hd1)) ^ " & " ^ (Ustring.to_utf8 (Pprint.pprint false hd2)) ^ "\n" ^ (get_tm_pair_list_string tl)

let rec get_tm_list_string l =
  match l with
  | [] -> "\n"
  | hd::tl ->
    "- " ^ (Ustring.to_utf8 (Pprint.pprint false hd)) ^ "\n" ^ (get_tm_list_string tl)

let rec get_rels_assoc_list_string rels_assoc_l =
  match rels_assoc_l with
  | [] -> "\n"
  | (hd,hdl)::tl ->
    (Ustring.to_utf8 (Pprint.pprint false hd)) ^ " is related to:\n" ^ (get_tm_list_string hdl) ^ (get_rels_assoc_list_string tl)

(*Help methods*)
let rec check_if_ty_is_seq ty =
  match ty with
  | TySeq _ ->
    true
  | TyArrow(_,_,TySeq _) ->
    true
  | TyArrow(_,_,rhs_ty) ->
    check_if_ty_is_seq rhs_ty
  | _ ->
    (*let _ = Printf.printf "%s does not have type TySeq\n" (Ustring.to_utf8 (Pprint.pprint_ty ty)) in*)
    false

let rec check_if_tm_is_seq t =
  match t, getType t with
  | TmLam(lam_ti,lam_x,lam_ty,lam_tm), ty ->
    (match ty with
     | TyArrow(_,TySeq _,TyGround(_,GVoid)) ->
       true
     | _ ->
       check_if_ty_is_seq ty
    )
  | _, ty ->
    check_if_ty_is_seq ty

let rec find_rels_and_seqs_in_ast ast rels seqs =
  let find_rels_and_seqs_in_tmapp tm1 tm2 =
    (match tm1, check_if_tm_is_seq tm2 with
     | TmLam(lam_ti,lam_x,lam_ty,TmNop), true ->
       let (rels_tm1,seqs_tm1) = find_rels_and_seqs_in_ast tm1 [] [] in
       let (rels_tm2, seqs_tm2) = find_rels_and_seqs_in_ast tm2 [] [] in
       (*TODO: Failwith if seqs_tm2 is empty*)
       let new_rel = (tm1,(List.nth seqs_tm2 0)) in
       let upd_rels = List.append (new_rel::rels_tm1) rels_tm2 in
       let upd_seqs = List.append seqs_tm1 seqs_tm2 in
       (upd_rels,upd_seqs)
     | _, true ->
       let (rels_tm1,seqs_tm1) = find_rels_and_seqs_in_ast tm1 [] [] in
       let (rels_tm2,seqs_tm2) = find_rels_and_seqs_in_ast tm2 [] [] in
       (*TODO: Failwith if seqs_tm2 is empty*)
       let new_rel = ((List.nth seqs_tm1 ((List.length seqs_tm1)-1)),(List.nth seqs_tm2 0)) in
       let upd_rels = List.append (new_rel::rels_tm1) rels_tm2 in
       let upd_seqs = List.append seqs_tm1 seqs_tm2 in
       (*let _ = Printf.printf "%s with %s\n" (Ustring.to_utf8 (Pprint.pprint false tm1)) (Ustring.to_utf8 (Pprint.pprint false tm2)) in
       let _ = Printf.printf "The LHS seqs are: %s\n" (get_tm_list_string seqs_tm1) in
       let _ = Printf.printf "The RHS seqs are: %s\n" (get_tm_list_string seqs_tm2) in*)
       (upd_rels,upd_seqs)
     | _ ->
       let (rels_tm1,seqs_tm1) = find_rels_and_seqs_in_ast tm1 [] [] in
       let (rels_tm2,seqs_tm2) = find_rels_and_seqs_in_ast tm2 [] [] in
       let upd_rels = List.append rels_tm1 rels_tm2 in
       let upd_seqs = List.append seqs_tm1 seqs_tm2 in
       (upd_rels,upd_seqs)) in
  let rec find_rels_and_seqs_in_ast_list l l_rels l_seqs =
    (match l with
     | [] -> (l_rels,l_seqs)
     | hd::tl ->
       let (upd_l_rels,upd_l_seqs) = find_rels_and_seqs_in_ast hd l_rels l_seqs in
       find_rels_and_seqs_in_ast_list tl upd_l_rels upd_l_seqs) in
  match ast with
  | TmSeq(ti,ty_ident,tm_l,tm_seq,ds_choice) ->
    let _ = check_if_tm_is_seq ast in (*TODO:Unnecessary*)
    let upd_seqs = ast::seqs in
    find_rels_and_seqs_in_ast_list (get_list_from_tmlist tm_l) rels upd_seqs
  | TmSeqMethod _ ->
    (rels,(ast::seqs))
  | TmNop ->
    (rels,seqs)
  | TmVar _ | TmChar _ | TmFix _ | TmConst _ ->
    if check_if_tm_is_seq ast then
      (rels,(ast::seqs))
    else
      (rels,seqs)
  | TmLam(_,_,_,tm) | TmClos(_,_,_,tm,_,_) ->
    let upd_seqs =
      (if check_if_tm_is_seq ast then
         ast::seqs
       else
         seqs) in
    find_rels_and_seqs_in_ast tm rels upd_seqs
  | TmApp(_,tm1,tm2) ->
    let (app_rels,app_seqs) = find_rels_and_seqs_in_tmapp tm1 tm2 in
    let upd_rels = List.append app_rels rels in
    let upd_seqs = List.append app_seqs seqs in
    (upd_rels,upd_seqs)
  | TmUtest(_,tm1,tm2,tm3) | TmIfexp(_,tm1,tm2,tm3) ->
    let (upd_seqs1) =
      (if check_if_tm_is_seq ast then
         ast::seqs
       else
         seqs) in
    let (upd_rels1,upd_seqs2) = find_rels_and_seqs_in_ast tm1 rels upd_seqs1 in
    let (upd_rels2,upd_seqs3) = find_rels_and_seqs_in_ast tm2 upd_rels1 upd_seqs2 in
    find_rels_and_seqs_in_ast tm3 upd_rels2 upd_seqs3
  | TmMatch _ | TmUC _ | TmTyApp _ | TmTyLam _ ->
    failwith "Not implemented"

let rec find_seq_cons_among_seqs seqs =
  match seqs with
  | [] -> []
  | hd::tl ->
    (match hd with
     | TmSeq _ ->
       hd::(find_seq_cons_among_seqs tl)
     | _ ->
       find_seq_cons_among_seqs tl
    )

let rec init_rels_assoc_list seqs =
  match seqs with
  | [] -> []
  | hd::tl ->
    (hd,[])::(init_rels_assoc_list tl)

let upd_rels_assoc_list_list_entry key rels_assoc_l new_val =
  let upd_rels_assoc_l1 =
    (if List.mem_assoc key rels_assoc_l then
       rels_assoc_l
     else
       (key,[])::rels_assoc_l) in
  let curr_val = List.assoc key upd_rels_assoc_l1 in
  let upd_val = new_val::curr_val in
  let upd_rels_assoc_l2 = List.remove_assoc key upd_rels_assoc_l1 in
  (key,upd_val)::upd_rels_assoc_l2

  let upd_rels_assoc_list_bool_entry key rels_assoc_l new_val =
    let upd_rels_assoc_l1 =
      (if List.mem_assoc key rels_assoc_l then
         rels_assoc_l
       else
         (key,false)::rels_assoc_l) in
    let upd_rels_assoc_l2 = List.remove_assoc key upd_rels_assoc_l1 in
    (key,new_val)::upd_rels_assoc_l2

(*let rec transl_rels_to_rels_assoc_list rels rels_assoc_l =
  match rels with
  | [] -> rels_assoc_l
  | (hd1,hd2)::tl ->
    let upd_rels_assoc_l = upd_rels_assoc_list_list_entry hd2 rels_assoc_l hd1 in
    transl_rels_to_rels_assoc_list tl upd_rels_assoc_l*)
let rec transl_rels_to_rels_assoc_list2 rels rels_assoc_l =
  match rels with
  | [] -> rels_assoc_l
  | (hd1,hd2)::tl ->
    let upd_rels_assoc_l1 = upd_rels_assoc_list_list_entry hd1 rels_assoc_l hd2 in
    let upd_rels_assoc_l2 = upd_rels_assoc_list_list_entry hd2 upd_rels_assoc_l1 hd1 in
    transl_rels_to_rels_assoc_list2 tl upd_rels_assoc_l2

let rec init_visited_seqs_assoc_list rels_assoc_l =
  match rels_assoc_l with
  | [] -> []
  | (hd,_)::tl ->
    (hd,false)::(init_visited_seqs_assoc_list tl)

let rec find_all_related_seqs rels_assoc_l curr_seqs new_seqs visited_assoc_l all_seqs =
  match curr_seqs, new_seqs with
  | [], [] -> (all_seqs,visited_assoc_l)
  | [], _ -> find_all_related_seqs rels_assoc_l new_seqs [] visited_assoc_l all_seqs
  | (hd::tl), _ ->
    if List.assoc hd visited_assoc_l then
      find_all_related_seqs rels_assoc_l tl new_seqs visited_assoc_l all_seqs
    else
      (*Mark hd as visited*)
      let upd_visited_assoc_l = upd_rels_assoc_list_bool_entry hd visited_assoc_l true in
      let hd_rel_seqs = List.assoc hd rels_assoc_l in
      let upd_new_seqs = List.append hd_rel_seqs new_seqs in
      let upd_all_seqs = hd::all_seqs in
      find_all_related_seqs rels_assoc_l tl upd_new_seqs upd_visited_assoc_l upd_all_seqs

let rec reduce_rels rels_assoc_l visited_assoc_l =
  match rels_assoc_l with
  | [] -> []
  | (hd,hdl)::tl ->
    if List.assoc hd visited_assoc_l then
      reduce_rels tl visited_assoc_l
    else
      (*Mark hd as visited*)
      let upd_visited_assoc_l1 = upd_rels_assoc_list_bool_entry hd visited_assoc_l true in
      (*Get all relatives of hd*)
      let (hd_rel_seqs,upd_visited_assoc_l2) = find_all_related_seqs rels_assoc_l (List.assoc hd rels_assoc_l) [] visited_assoc_l [] in
      (hd,hd_rel_seqs)::(reduce_rels rels_assoc_l upd_visited_assoc_l2)

let process_ast ast =
  let _ = Printf.printf "The program is %s\n" (Ustring.to_utf8 (Pprint.pprint false ast)) in
  (*Find all terms of sequence type and sequence methods, and their internal relationships*)
  let (rels,seqs) = find_rels_and_seqs_in_ast ast [] [] in
  let _ = Printf.printf "The seqs:\n%s\n" (get_tm_list_string seqs) in
  let _ = Printf.printf "The rels:\n%s\n" (get_tm_pair_list_string rels) in
  (*Get the sequence constructors*)
  let seq_cons = find_seq_cons_among_seqs seqs in
  let _ = Printf.printf "The seq cons:\n%s\n" (get_tm_list_string seq_cons) in
  (*Initate association list for relationships*)
  let rels_assoc_l1 = init_rels_assoc_list seqs in
  let _ = Printf.printf "The first version of the rels assoc list:\n%s\n" (get_rels_assoc_list_string rels_assoc_l1) in
  (*Transfer relationships in rels to the rels assoc list*)
  let rels_assoc_l2 = transl_rels_to_rels_assoc_list2 rels rels_assoc_l1 in
  let _ = Printf.printf "The second version of the rels assoc list:\n%s\n" (get_rels_assoc_list_string rels_assoc_l2) in
  let rels_assoc_l3 = reduce_rels rels_assoc_l2 (init_visited_seqs_assoc_list rels_assoc_l2) in
  let _ = Printf.printf "The third version of the rels assoc list:\n%s\n" (get_rels_assoc_list_string rels_assoc_l3) in
  ast
