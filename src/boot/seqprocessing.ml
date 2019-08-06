open Ast
open Dssa
open Linkedlist
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

let rec get_mf_count_string_helper mf_row =
  match mf_row with
  | [] -> "-------\n"
  | (hd,hd_count)::tl ->
    "- " ^ hd ^ " with count " ^ (string_of_int hd_count) ^ "\n" ^ (get_mf_count_string_helper tl)

let rec get_mf_count_string mf_matrix =
  match mf_matrix with
  | [] -> "\n"
  | hd::tl ->
    "\n ----START---- \n" ^ (get_mf_count_string_helper hd) ^ "\n" ^ (get_mf_count_string tl)

let rec get_mf_freq_row_string mf_row =
  match mf_row with
  | [] -> "/"
  | hd::tl ->
    (Frequencies.to_string hd) ^ " " ^ (get_mf_freq_row_string tl)

let rec get_mf_freq_string mf_matrix =
  match mf_matrix with
  | [] -> "\n"
  | hd::tl ->
    (get_mf_freq_row_string hd) ^ "\n" ^ (get_mf_freq_string tl)

let rec get_selected_datastructures_string selected_dss =
  match selected_dss with
  | [] -> "\n"
  | hd::tl ->
    "- " ^ (string_of_int (List.nth hd 0)) ^ "\n" ^ (get_selected_datastructures_string tl)

let rec get_seqs_w_selected_dss_string selected_ds_assoc_l =
  match selected_ds_assoc_l with
  | [] -> "\n"
  | (hd1,hd2)::tl ->
    "- " ^ (Ustring.to_utf8 (Pprint.pprint false hd1)) ^ " with data structure " ^ (string_of_int hd2) ^ "\n" ^ (get_seqs_w_selected_dss_string tl)

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

let rec find_related_vars lam_x seqs =
  match seqs with
  | [] -> []
  | hd::tl ->
    (match hd with
     | TmVar(_,var_x,_,_) ->
       if (Ustring.to_utf8 var_x) = (Ustring.to_utf8 lam_x) then
         hd::(find_related_vars lam_x tl)
       else
         find_related_vars lam_x tl
     | _ ->
       find_related_vars lam_x tl)

let rec get_lam_var_rels lam vars =
  match vars with
  | [] -> []
  | hd::tl ->
    (lam,hd)::(get_lam_var_rels lam tl)

let rec find_rels_and_seqs_in_ast ast rels seqs =
  (*let _ = Printf.printf "- %s with type %s\n" (Ustring.to_utf8 (Pprint.pprint false ast)) (Ustring.to_utf8 (Pprint.pprint_ty (Typesys.getType ast))) in*)
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
  | TmVar(ti,x,di,pm) ->
    if check_if_tm_is_seq ast then
      (rels,(ast::seqs))
    else
      (rels,seqs)
  | TmChar _ | TmFix _ | TmConst _ ->
    if check_if_tm_is_seq ast then
      (rels,(ast::seqs))
    else
      (rels,seqs)
  | TmLam(_,x,_,tm)  ->
    let (upd_seqs) =
      (if check_if_tm_is_seq ast then
         (ast::seqs)
       else
         seqs) in
    find_rels_and_seqs_in_ast tm rels upd_seqs
  | TmClos(_,_,_,tm,_,_) ->
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
    failwith "Not implemented1"

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
let rec transl_rels_to_rels_assoc_list rels rels_assoc_l =
  match rels with
  | [] -> rels_assoc_l
  | (hd1,hd2)::tl ->
    let upd_rels_assoc_l1 = upd_rels_assoc_list_list_entry hd1 rels_assoc_l hd2 in
    let upd_rels_assoc_l2 = upd_rels_assoc_list_list_entry hd2 upd_rels_assoc_l1 hd1 in
    transl_rels_to_rels_assoc_list tl upd_rels_assoc_l2

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
      let (hd_rel_seqs,upd_visited_assoc_l2) = find_all_related_seqs rels_assoc_l (List.assoc hd rels_assoc_l) [] upd_visited_assoc_l1 [] in
      (hd,hd_rel_seqs)::(reduce_rels rels_assoc_l upd_visited_assoc_l2)

let get_seq_fun_names =
  (*TODO: Get this from somewhere else*)
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
   "foldl"]

let rec init_fun_count_assoc_list funs =
  match funs with
  | [] -> []
  | hd::tl ->
    (hd,0)::(init_fun_count_assoc_list tl)

let init_mf_row =
  let fun_names = get_seq_fun_names in
  init_fun_count_assoc_list fun_names

let rec get_seqmethods seqs =
  match seqs with
  | [] -> []
  | hd::tl ->
    (match hd with
     | TmSeqMethod _ -> hd::(get_seqmethods tl)
     | _ -> get_seqmethods tl
    )

let get_seqm_fun_name_string seqm =
  match seqm with
  | TmSeqMethod(_,fun_name,_,_,_,_) -> (Ustring.to_utf8 fun_name)
  | _ -> failwith "Expected a TmSeqMethod"

let rec fill_in_mf_row mf_row seqms =
  match seqms with
  | [] -> mf_row
  | hd::tl ->
    let fun_name = get_seqm_fun_name_string hd in
    let curr_fun_count = List.assoc fun_name mf_row in
    let upd_fun_count = curr_fun_count + 1 in
    let upd_mf_row1 = List.remove_assoc fun_name mf_row in
    let upd_mf_row2 = (fun_name,upd_fun_count)::upd_mf_row1 in
    fill_in_mf_row upd_mf_row2 tl

let rec create_mf_matrix rels_assoc_l =
  match rels_assoc_l with
  | [] -> []
  | (hd,hdl)::tl ->
    let mf_row = init_mf_row in
    let seqms = get_seqmethods hdl in
    let upd_mf_row = fill_in_mf_row mf_row seqms in
    upd_mf_row::(create_mf_matrix tl)

let rec find_lam_var_rels seqs rels seqs_unchanged =
  match seqs with
  | [] -> rels
  | hd::tl ->
    (match hd with
     | TmLam(_,x,_,_) ->
       let rel_vars = find_related_vars x seqs_unchanged in
       let lam_var_rels = get_lam_var_rels hd (rel_vars) in
       let new_rels = List.append lam_var_rels rels in
       find_lam_var_rels tl new_rels seqs_unchanged
     | _ ->
       find_lam_var_rels tl rels seqs_unchanged
    )

let rec connect_seqs_list_w_sel_ds sel_ds seq_l =
  match seq_l with
  | [] -> []
  | hd::tl ->
    (hd,sel_ds)::(connect_seqs_list_w_sel_ds sel_ds tl)

let rec connect_seqs_w_sel_dss selected_dss rels_assoc_l =
  match selected_dss, rels_assoc_l with
  | [], [] -> []
  | [], _ | _, [] -> failwith "The lists should have the same length"
  | (hd1::tl1), ((hd2,hdl2)::tl2) ->
    let new_entry = (hd2,(List.nth hd1 0)) in
    let new_entries = connect_seqs_list_w_sel_ds (List.nth hd1 0) hdl2 in
    List.append (new_entry::new_entries) (connect_seqs_w_sel_dss tl1 tl2)

let get_actual_fun_w_sel_ds fun_name sel_ds =
  match sel_ds, (Ustring.to_utf8 fun_name) with
  | 0, "is_empty" -> (SeqListFun4(Linkedlist.is_empty))
  | 0, "first" -> (SeqListFun5(Linkedlist.first))
  | 0, "last" -> (SeqListFun5(Linkedlist.last))
  | 0, "push" -> (SeqListFun3(Linkedlist.push))
  | 0, "pop" -> (SeqListFun6(Linkedlist.pop))
  | 0, "length" -> (SeqListFun2(Linkedlist.length))
  | 0, "nth" -> (SeqListFun7(Linkedlist.nth))
  | 0, "append" -> (SeqListFun1(Linkedlist.append))
  | 0, "reverse" -> (SeqListFun6(Linkedlist.reverse))
  | 0, "push_last" -> (SeqListFun3(Linkedlist.push_last))
  | 0, "pop_last" -> (SeqListFun6(Linkedlist.pop_last))
  | 0, "take" -> (SeqListFun8(Linkedlist.take))
  | 0, "drop" -> (SeqListFun8(Linkedlist.drop))
  | 0, "map" -> (SeqListFun9(Linkedlist.map))
  | 0, "any" -> (SeqListFun10(Linkedlist.any))
  | 0, "seqall" -> (SeqListFun10(Linkedlist.all))
  | 0, "find" -> (SeqListFun11(Linkedlist.find))
  | 0, "filter" -> (SeqListFun12(Linkedlist.filter))
  | 0, "foldr" -> (SeqListFun13(Linkedlist.foldr))
  | 0, "foldl" -> (SeqListFun13(Linkedlist.foldl))
  | _ -> failwith "Method not yet implemented1"

let rec update_ast_w_sel_dss ast sel_dss =
  let rec update_ast_list_w_sel_dss ast_l sel_dss' =
    (match ast_l with
     | [] -> []
     | hd::tl ->
       let upd_hd = update_ast_w_sel_dss hd sel_dss' in
       upd_hd::(update_ast_list_w_sel_dss tl sel_dss')) in
  match ast with
  | TmSeq(ti,ty_ident,tm_l,tm_seq,ds_choice) ->
    let upd_tm_l = update_ast_list_w_sel_dss (get_list_from_tmlist tm_l) sel_dss in
    let upd_ds_choice = List.assoc ast sel_dss in
    TmSeq(ti,ty_ident,TmList(upd_tm_l),tm_seq,upd_ds_choice)
  | TmSeqMethod(ti,fun_name,actual_fun,args,arg_index,ds_choice) ->
    let upd_ds_choice = List.assoc ast sel_dss in
    let upd_actual_fun = get_actual_fun_w_sel_ds fun_name upd_ds_choice in
    TmSeqMethod(ti,fun_name,upd_actual_fun,args,arg_index,upd_ds_choice)
  | TmNop | TmVar _ | TmChar _ | TmFix _ | TmConst _ -> ast
  | TmLam(ti,x,ty,tm) ->
    let upd_tm = update_ast_w_sel_dss tm sel_dss in
    TmLam(ti,x,ty,upd_tm)
  | TmClos(ti,x,ty,tm,env,pm) ->
    let upd_tm = update_ast_w_sel_dss tm sel_dss in
    TmClos(ti,x,ty,upd_tm,env,pm)
  | TmApp(ti,tm1,tm2) ->
    let upd_tm1 = update_ast_w_sel_dss tm1 sel_dss in
    let upd_tm2 = update_ast_w_sel_dss tm2 sel_dss in
    TmApp(ti,upd_tm1,upd_tm2)
  | TmUtest(ti,tm1,tm2,tm3) ->
    let upd_tm1 = update_ast_w_sel_dss tm1 sel_dss in
    let upd_tm2 = update_ast_w_sel_dss tm2 sel_dss in
    let upd_tm3 = update_ast_w_sel_dss tm3 sel_dss in
    TmUtest(ti,upd_tm1,upd_tm2,upd_tm3)
  | TmIfexp(ti,tm1,tm2,tm3) ->
    let upd_tm1 = update_ast_w_sel_dss tm1 sel_dss in
    let upd_tm2 = update_ast_w_sel_dss tm2 sel_dss in
    let upd_tm3 = update_ast_w_sel_dss tm3 sel_dss in
    TmIfexp(ti,upd_tm1,upd_tm2,upd_tm3)
  | TmMatch _ | TmUC _ | TmTyApp _ | TmTyLam _ ->
    failwith "Not implemented2"

let process_ast ast =
  let _ = Printf.printf "\nThe complete program is:\n%s\n" (Ustring.to_utf8 (Pprint.pprint false ast)) in
  (*Find all terms of sequence type and sequence methods, and their internal relationships*)
  let (rls,seqs) = find_rels_and_seqs_in_ast ast [] [] in
  let rels = find_lam_var_rels seqs rls seqs in
  (*let _ = Printf.printf "The seqs:\n%s\n" (get_tm_list_string seqs) in
  let _ = Printf.printf "The rels:\n%s\n" (get_tm_pair_list_string rels) in*)
  (*Get the sequence constructors*)
  let seq_cons = find_seq_cons_among_seqs seqs in
  (*let _ = Printf.printf "The seq cons:\n%s\n" (get_tm_list_string seq_cons) in*)
  (*Initate association list for relationships*)
  let rels_assoc_l1 = init_rels_assoc_list seqs in
  (*let _ = Printf.printf "The first version of the rels assoc list:\n%s\n" (get_rels_assoc_list_string rels_assoc_l1) in*)
  (*Transfer relationships in rels to the rels assoc list*)
  let rels_assoc_l2 = transl_rels_to_rels_assoc_list rels rels_assoc_l1 in
  (*let _ = Printf.printf "The second version of the rels assoc list:\n%s\n" (get_rels_assoc_list_string rels_assoc_l2) in*)
  (*Reduce relationships*)
  let rels_assoc_l3 = reduce_rels rels_assoc_l2 (init_visited_seqs_assoc_list rels_assoc_l2) in
  (*let _ = Printf.printf "The third version of the rels assoc list:\n%s\n" (get_rels_assoc_list_string rels_assoc_l3) in*)
  (*Create Method-Frequency (MF) matrix*)
  let mf_matrix1 = create_mf_matrix rels_assoc_l3 in
  (*let _ = Printf.printf "The first version of the mf matrix:\n%s\n" (get_mf_count_string mf_matrix1) in*)
  (*Translate MF count to MF frequencies*)
  let mf_matrix2 = Frequencies.translate_mf_assoc_list mf_matrix1 (get_seq_fun_names) in
  (*let _ = Printf.printf "The second version of the mf matrix:\n%s\n" (get_mf_freq_string mf_matrix2) in*)
  (*Data structure selection algorithm*)
  let selected_dss = Dssa.main mf_matrix2 in
  (*let _ = Printf.printf "The selected data structures are:\n%s\n" (get_selected_datastructures_string selected_dss) in*)
  (*Connect selected data structure with all seqs*)
  let sel_dss_assoc_l = connect_seqs_w_sel_dss selected_dss rels_assoc_l3 in
  (*let _ = Printf.printf "The seqs with selected data structures are:\n%s\n" (get_seqs_w_selected_dss_string sel_dss_assoc_l) in*)
  (*Update ast with selected data structures*)
  let upd_ast = update_ast_w_sel_dss ast sel_dss_assoc_l in
  (*let _ = Printf.printf "The updated ast is:\n%s\n" (Ustring.to_utf8 (Pprint.pprint false upd_ast)) in*)
  upd_ast
