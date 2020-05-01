open Ast
open Dssa
open Linkedlist
open Ocamlarray
open Ocamlqueue
open Ocamlstack
open Okasakiqueue
open Fingertree
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
let rec check_if_ty_is_tyseq ty =
  match ty with
  (*All terms of type TySeq*)
  | TySeq _ ->
    true
  (*All terms "returning" a term of type TySeq*)
  | TyArrow(_,_,TySeq _) ->
    true
  (*The case of nested TyArrows*)
  | TyArrow(_,_,rhs_ty) ->
    check_if_ty_is_tyseq rhs_ty
  | _ ->
    false

let rec check_if_tm_has_type_tyseq t =
  match t, getType t with
  | TmLam(lam_ti,lam_x,lam_ty,lam_tm), ty ->
    (match ty with
     (*The special case "let x = term of type TySeq"*)
     | TyArrow(_,TySeq _,TyGround(_,GVoid)) ->
       true
     | _ ->
       check_if_ty_is_tyseq ty
    )
  | _, ty ->
    check_if_ty_is_tyseq ty

(*Finds all vars in list "seqs" that has the identifier "lam_x"*)
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

(*Forms pairs between lambda "lam" and each variable in the list "vars"*)
let rec get_lam_var_rels lam vars =
  match vars with
  | [] -> []
  | hd::tl ->
    (lam,hd)::(get_lam_var_rels lam tl)

let rec combine_new_tm_var_rels e l =
  match l with
  | [] -> []
  | hd::tl ->
    (e,hd)::(combine_new_tm_var_rels e tl)

let compare_names var_x y =
  match y with
  | TmVar(_,var_y,_,_) ->
    (Ustring.to_utf8 var_x) = (Ustring.to_utf8 var_y)
  | _ -> false

let rec find_vars_with_the_same_name seqs =
  match seqs with
  | [] -> []
  | hd::tl ->
    (
      match hd with
      | TmVar(_,var_x,_,_) ->
        let matches = List.find_all (compare_names var_x) tl in
        let new_rels = combine_new_tm_var_rels hd matches in
        List.append new_rels (find_vars_with_the_same_name tl)
      | _ -> find_vars_with_the_same_name tl
    )

(*Goes through AST to find all terms of sequence type and their internal relationships*)
let rec find_rels_and_seqs_in_ast ast rels seqs in_fix =
  (*let _ = Printf.printf "- %s with type %s\n" (Ustring.to_utf8 (Pprint.pprint false ast)) (Ustring.to_utf8 (Pprint.pprint_ty (Typesys.getType ast))) in*)
  (*Processes terms from an application (TmApp)*)
  let find_rels_and_seqs_in_tmapp tm1 tm2 in_fix' =
    (match tm1, check_if_tm_has_type_tyseq tm2 with
     (*If tm1 is a fix, then we want to keep track of this when processing tm2 and therefore call find_rels_and_seqs_in_ast with in_fix (last arg) set to true*)
     | TmFix(fix_ti), _ ->
       find_rels_and_seqs_in_ast tm2 [] [] true
     (*The case "let x = exp of type seq"*)
     | TmLam(lam_ti,lam_x,lam_ty,TmNop), true ->
       let (rels_tm1,seqs_tm1) = find_rels_and_seqs_in_ast tm1 [] [] in_fix' in
       let (rels_tm2, seqs_tm2) = find_rels_and_seqs_in_ast tm2 [] [] in_fix' in
       (*TODO: Failwith if seqs_tm2 is empty*)
       (*Lambda term (tm1) and the first sequence in tm2 are related*)
       let new_rel = (tm1,(List.nth seqs_tm2 0)) in
       let upd_rels = List.append (new_rel::rels_tm1) rels_tm2 in
       let upd_seqs = List.append seqs_tm1 seqs_tm2 in
       (upd_rels,upd_seqs)
     (*The case "tm1 tm2" where tm2 has type sequence*)
     | _, true ->
       let (rels_tm1,seqs_tm1) = find_rels_and_seqs_in_ast tm1 [] [] in_fix' in
       let (rels_tm2,seqs_tm2) = find_rels_and_seqs_in_ast tm2 [] [] in_fix' in
       let upd_rels = List.append rels_tm1 rels_tm2 in
       let upd_seqs = List.append seqs_tm1 seqs_tm2 in
       if ((List.length seqs_tm1) == 0) || ((List.length seqs_tm2) == 0) then
         (upd_rels,upd_seqs)
       else
         (*The last sequence found in tm1 is related to the first sequence found in tm2*)
         let new_rel = ((List.nth seqs_tm1 ((List.length seqs_tm1)-1)),(List.nth seqs_tm2 0)) in
         ((new_rel::upd_rels),upd_seqs)
     | _ ->
       let (rels_tm1,seqs_tm1) = find_rels_and_seqs_in_ast tm1 [] [] in_fix' in
       let (rels_tm2,seqs_tm2) = find_rels_and_seqs_in_ast tm2 [] [] in_fix' in
       let upd_rels = List.append rels_tm1 rels_tm2 in
       let upd_seqs = List.append seqs_tm1 seqs_tm2 in
       (upd_rels,upd_seqs)) in
  (*Processes terms in a list (TmList) as found in a sequence constructor (TmSeq)*)
  let rec find_rels_and_seqs_in_ast_list l l_rels l_seqs l_in_fix =
    (match l with
     | [] -> (l_rels,l_seqs)
     | hd::tl ->
       let (upd_l_rels,upd_l_seqs) = find_rels_and_seqs_in_ast hd l_rels l_seqs l_in_fix in
       find_rels_and_seqs_in_ast_list tl upd_l_rels upd_l_seqs l_in_fix) in
  match ast with
  | TmSeq(ti,ty_ident,tm_l,tm_seq,ds_choice) ->
    (*TmSeq always has type TySeq*)
    let upd_seqs = ast::seqs in
    (*Process elements (terms) of the sequence*)
    find_rels_and_seqs_in_ast_list (get_list_from_tmlist tm_l) rels upd_seqs in_fix
  | TmSeqMethod(seqm_ti,fun_name,actual_fun,args,arg_index,ds_choice,in_fix_unknown) ->
    (*We want to keep track of whether the sequence method is contained within a recursive method (application of TmFix), and therefore update the in_fix field of the TmSeqMethod*)
    let upd_seqm = TmSeqMethod(seqm_ti,fun_name,actual_fun,args,arg_index,ds_choice,in_fix) in
    (*We always consider a sequence method as an instance of sequence, even if it doesn't return a sequence*)
    let upd_seqs = upd_seqm::seqs in
    (rels,upd_seqs)
  | TmNop | TmChar _ | TmFix _ | TmConst _ ->
    (rels,seqs)
  | TmVar(ti,x,di,pm) ->
    (*If the variable has type sequence, then we want to add it to our list of sequences found*)
    if check_if_tm_has_type_tyseq ast then
      (rels,(ast::seqs))
    else
      (rels,seqs)
  | TmLam(_,_,_,tm) | TmClos(_,_,_,tm,_,_)  ->
    (*If the lambda/closure has type sequence, then we want to add it to our list of sequences found*)
    let (upd_seqs) =
      (if check_if_tm_has_type_tyseq ast then
         (ast::seqs)
       else
         seqs) in
    (*We also want to process the term found within the lambda/closure*)
    find_rels_and_seqs_in_ast tm rels upd_seqs in_fix
  | TmApp(_,tm1,tm2) ->
    (*We want to process the two terms within the application to determine how they relate to each other*)
    let (app_rels,app_seqs) = find_rels_and_seqs_in_tmapp tm1 tm2 in_fix in
    let upd_rels = List.append app_rels rels in
    let upd_seqs = List.append app_seqs seqs in
    (upd_rels,upd_seqs)
  | TmUtest(_,tm1,tm2,tm3) | TmIfexp(_,tm1,tm2,tm3) ->
    (*If the test/if expression has type sequence, then we want to add it to our list of sequences found*)
    let (upd_seqs1) =
      (if check_if_tm_has_type_tyseq ast then
         ast::seqs
       else
         seqs) in
    (*We also want to process the terms found within the test/if expression*)
    let (upd_rels1,upd_seqs2) = find_rels_and_seqs_in_ast tm1 rels upd_seqs1 in_fix in
    let (upd_rels2,upd_seqs3) = find_rels_and_seqs_in_ast tm2 upd_rels1 upd_seqs2 in_fix in
    find_rels_and_seqs_in_ast tm3 upd_rels2 upd_seqs3 in_fix
  (*Cases not yet implemented*)
  | TmMatch _ ->
    failwith "Not implemented1"
  | TmUC _ ->
    failwith "Not implemented2"
  | TmTyApp(app_ti,app_tm,app_ty) ->
    failwith "Not implemented3"
  | TmTyLam _ ->
    failwith "Not implemented4"

(*Find the sequence constructors - that is, TmSeq terms - in a list of terms*)
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

(*Initialize an association list where they key is a term and the value is an empty list.*)
let rec init_rels_assoc_list seqs =
  match seqs with
  | [] -> []
  | hd::tl ->
    (hd,[])::(init_rels_assoc_list tl)

(*Update an association list entry where they key is a term and the value is a list. The argument "new_val" is the value we want to add to the list associated with "key".*)
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

(*Update an association list entry where they key is a term and the value is a boolean. The argument "new_val" is the new boolean value we want to associate with "key".*)
let upd_rels_assoc_list_bool_entry key rels_assoc_l new_val =
  let upd_rels_assoc_l1 =
    (if List.mem_assoc key rels_assoc_l then
       rels_assoc_l
     else
       (key,false)::rels_assoc_l) in
  let upd_rels_assoc_l2 = List.remove_assoc key upd_rels_assoc_l1 in
  (key,new_val)::upd_rels_assoc_l2

(*Translates a list of relationships - that is, term pairs - to an association list where they key is a term and the value is a list of its related terms. "rels" is the list of relationships and "rels_assoc_l" is an initialized association list.*)
let rec transl_rels_to_rels_assoc_list rels rels_assoc_l =
  match rels with
  | [] -> rels_assoc_l
  | (hd1,hd2)::tl ->
    (*Add relationship (hd1,hd2) to association list*)
    let upd_rels_assoc_l1 = upd_rels_assoc_list_list_entry hd1 rels_assoc_l hd2 in
    (*Add relationship (hd2,hd1) to association list*)
    let upd_rels_assoc_l2 = upd_rels_assoc_list_list_entry hd2 upd_rels_assoc_l1 hd1 in
    transl_rels_to_rels_assoc_list tl upd_rels_assoc_l2

(*Initializes an association list for keeping track of which terms have been visited. The key is a term and the value, which is a boolean, is initially set to false.*)
let rec init_visited_seqs_assoc_list rels_assoc_l =
  match rels_assoc_l with
  | [] -> []
  | (hd,_)::tl ->
    (hd,false)::(init_visited_seqs_assoc_list tl)

(*Dives further down into the association list for relationships to find all terms related to "curr_seqs".
  Input:
  - "rels_assoc_l" is an association list where the key is a term and the value is a list with all its related terms
  - "curr_seqs" is the list of sequences for which we currently want to find all relatives
  - "new_seqs" is a list of sequences recently found for which we later want to find all relatives
  - "visited_assoc_l" is an association list where the key is a term and the value is a boolean, which is used to keep track of which terms have been visited
  - "all_seqs" is a list containing all related terms found so far
  Returns:
  - "all_seqs"
  - "visited_assoc_l"
*)
let rec find_all_related_seqs rels_assoc_l curr_seqs new_seqs visited_assoc_l all_seqs =
  match curr_seqs, new_seqs with
  (*All related terms have been found*)
  | [], [] -> (all_seqs,visited_assoc_l)
  (*All terms in "curr_seqs" have been visited, so we start to visit the terms in "new_seqs" instead*)
  | [], _ -> find_all_related_seqs rels_assoc_l new_seqs [] visited_assoc_l all_seqs
  | (hd::tl), _ ->
    if List.assoc hd visited_assoc_l then
      (*If term hd has already been visited, we continue on to the next element of the list "curr_seqs"*)
      find_all_related_seqs rels_assoc_l tl new_seqs visited_assoc_l all_seqs
    else
      (*Mark hd as visited*)
      let upd_visited_assoc_l = upd_rels_assoc_list_bool_entry hd visited_assoc_l true in
      (*Find the terms directly related to term hd*)
      let hd_rel_seqs = List.assoc hd rels_assoc_l in
      (*Add hd's related terms to the list for terms to study later*)
      let upd_new_seqs = List.append hd_rel_seqs new_seqs in
      (*Add hd to the list containing all related terms*)
      let upd_all_seqs = hd::all_seqs in
      (*Continue on to the next element of the list "curr_seqs"*)
      find_all_related_seqs rels_assoc_l tl upd_new_seqs upd_visited_assoc_l upd_all_seqs

(**)
let rec reduce_rels rels_assoc_l visited_assoc_l =
  match rels_assoc_l with
  | [] -> []
  | (hd,hdl)::tl ->
    if List.assoc hd visited_assoc_l then
      reduce_rels tl visited_assoc_l
    else
      (*Mark hd as visited*)
      let upd_visited_assoc_l1 = upd_rels_assoc_list_bool_entry hd visited_assoc_l true in
      (*Get all hd's related terms*)
      let (hd_rel_seqs,upd_visited_assoc_l2) = find_all_related_seqs rels_assoc_l (List.assoc hd rels_assoc_l) [] upd_visited_assoc_l1 [] in
      (*Add new entry with hd as key and all hd's related terms as value, and recursively continue building list for the next term in "rels_assoc_l"*)
      (hd,hd_rel_seqs)::(reduce_rels rels_assoc_l upd_visited_assoc_l2)

(*Initialize an association list where the key is a function name and the value is a count, which is initially set to zero.*)
let rec init_fun_count_assoc_list funs =
  match funs with
  | [] -> []
  | hd::tl ->
    (hd,0)::(init_fun_count_assoc_list tl)

(*Initialize an mf matrix row, where the keys are function names and the values are the count for that function, which is intially set to zero.*)
let init_mf_row =
  let fun_names = Sequenceinfo.get_seq_fun_names in
  init_fun_count_assoc_list fun_names

(*Finds all sequence methods - that is, TmSeqMethod - in a list of terms of type sequence.*)
let rec get_seqmethods seqs =
  match seqs with
  | [] -> []
  | hd::tl ->
    (match hd with
     | TmSeqMethod _ -> hd::(get_seqmethods tl)
     | _ -> get_seqmethods tl
    )

(*Get the function name from a sequence method term (TmSeqMethod).*)
let get_seqm_fun_name_string seqm =
  match seqm with
  | TmSeqMethod(_,fun_name,_,_,_,_,_) -> (Ustring.to_utf8 fun_name)
  | _ -> failwith "Expected a TmSeqMethod"

(*Get the "in_fix" boolean field from a sequence method term (TmSeqMethod).*)
let get_seqm_in_fix_bool seqm =
  match seqm with
  | TmSeqMethod(_,_,_,_,_,_,in_fix) -> in_fix
  | _ -> failwith "Expected a TmSeqMethod"

(*Fills in an mf matrix row "mf_row" with the count from a list of sequence methods "seqms"*)
let rec fill_in_mf_row mf_row seqms =
  match seqms with
  | [] -> mf_row
  | hd::tl ->
    let fun_name = get_seqm_fun_name_string hd in
    let curr_fun_count = List.assoc fun_name mf_row in
    let upd_fun_count =
      (if get_seqm_in_fix_bool hd || (curr_fun_count == -1) then
         -1
       else
         curr_fun_count + 1) in
    let upd_mf_row1 = List.remove_assoc fun_name mf_row in
    (*Add entry with incremented count for the current function name*)
    let upd_mf_row2 = (fun_name,upd_fun_count)::upd_mf_row1 in
    fill_in_mf_row upd_mf_row2 tl

(*Creates a mf matrix with one row for each entry in the "rels_assoc_l". Each row is an association list where they keys are function names and the values are the counts corresponding to function used in the code.*)
let rec create_mf_matrix rels_assoc_l =
  match rels_assoc_l with
  | [] -> []
  | (hd,hdl)::tl ->
    let mf_row = init_mf_row in
    let seqms = get_seqmethods hdl in
    let upd_mf_row = fill_in_mf_row mf_row seqms in
    upd_mf_row::(create_mf_matrix tl)

(*Connects lambda expressions in the list of sequences "seqs" with variables with the same identifier also found in "seqs".*)
let rec find_lam_var_rels seqs rels seqs_unchanged =
  match seqs with
  | [] -> rels
  | hd::tl ->
    (match hd with
     | TmLam(_,x,_,_) ->
       (*Find all related variables with the same identifier "x" in the list of sequences "seqs_unchanged"*)
       let rel_vars = find_related_vars x seqs_unchanged in
       (*Form relationships between the lambda and each related variable - that is, term pairs*)
       let lam_var_rels = get_lam_var_rels hd (rel_vars) in
       (*Add the newly formed relationships to the list containing all relationships found so far*)
       let upd_rels = List.append lam_var_rels rels in
       find_lam_var_rels tl upd_rels seqs_unchanged
     | _ ->
       find_lam_var_rels tl rels seqs_unchanged
    )

(*Associates sequences in "seq_l" with a selected data structure "sel_ds"*)
let rec connect_seqs_list_w_sel_ds sel_ds seq_l =
  match seq_l with
  | [] -> []
  | hd::tl ->
    (hd,sel_ds)::(connect_seqs_list_w_sel_ds sel_ds tl)

(*Takes in a list of selected data structures where each index represents a sequence and an association list with reduced relationships. Associates each sequence with the corresponding selected data structure.*)
let rec connect_seqs_w_sel_dss selected_dss rels_assoc_l =
  match selected_dss, rels_assoc_l with
  | [], [] -> []
  | [], _ | _, [] -> failwith "The lists should have the same length"
  | (hd1::tl1), ((hd2,hdl2)::tl2) ->
    (*Connect the key (hd) in the "rels_assoc_l" with the current selected data structure*)
    let new_entry = (hd2,(List.nth hd1 0)) in (*TODO:Collect from selected_dss, also below*)
    (*Connect all hd's related terms with the current selected data structure*)
    let new_entries = connect_seqs_list_w_sel_ds (List.nth hd1 0) hdl2 in
    List.append (new_entry::new_entries) (connect_seqs_w_sel_dss tl1 tl2)

(*Returns a function implementation given a fnuction name and a data structrue choice.*)
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
  | 0, "copy" -> (SeqListFun6(Linkedlist.copy))
  | 1, "is_empty" -> (SeqQueueFun4(Okasakiqueue.is_empty))
  | 1, "first" -> (SeqQueueFun5(Okasakiqueue.first))
  | 1, "last" -> (SeqQueueFun5(Okasakiqueue.last))
  | 1, "push" -> (SeqQueueFun3(Okasakiqueue.push))
  | 1, "pop" -> (SeqQueueFun6(Okasakiqueue.pop))
  | 1, "length" -> (SeqQueueFun2(Okasakiqueue.length))
  | 1, "nth" -> (SeqQueueFun7(Okasakiqueue.nth))
  | 1, "append" -> (SeqQueueFun1(Okasakiqueue.append))
  | 1, "reverse" -> (SeqQueueFun6(Okasakiqueue.reverse))
  | 1, "push_last" -> (SeqQueueFun3(Okasakiqueue.push_last))
  | 1, "pop_last" -> (SeqQueueFun6(Okasakiqueue.pop_last))
  | 1, "take" -> (SeqQueueFun8(Okasakiqueue.take))
  | 1, "drop" -> (SeqQueueFun8(Okasakiqueue.drop))
  | 1, "map" -> (SeqQueueFun9(Okasakiqueue.map))
  | 1, "any" -> (SeqQueueFun10(Okasakiqueue.any))
  | 1, "seqall" -> (SeqQueueFun10(Okasakiqueue.all))
  | 1, "find" -> (SeqQueueFun11(Okasakiqueue.find))
  | 1, "filter" -> (SeqQueueFun12(Okasakiqueue.filter))
  | 1, "foldr" -> (SeqQueueFun13(Okasakiqueue.foldr))
  | 1, "foldl" -> (SeqQueueFun13(Okasakiqueue.foldl))
  | 1, "copy" -> (SeqQueueFun6(Okasakiqueue.copy))
  | 2, "is_empty" -> (SeqOArrayFun4(Ocamlarray.is_empty))
  | 2, "first" -> (SeqOArrayFun5(Ocamlarray.first))
  | 2, "last" -> (SeqOArrayFun5(Ocamlarray.last))
  | 2, "push" -> (SeqOArrayFun3(Ocamlarray.push))
  | 2, "pop" -> (SeqOArrayFun6(Ocamlarray.pop))
  | 2, "length" -> (SeqOArrayFun2(Ocamlarray.length))
  | 2, "nth" -> (SeqOArrayFun7(Ocamlarray.nth))
  | 2, "append" -> (SeqOArrayFun1(Ocamlarray.append))
  | 2, "reverse" -> (SeqOArrayFun6(Ocamlarray.reverse))
  | 2, "push_last" -> (SeqOArrayFun3(Ocamlarray.push_last))
  | 2, "pop_last" -> (SeqOArrayFun6(Ocamlarray.pop_last))
  | 2, "take" -> (SeqOArrayFun8(Ocamlarray.take))
  | 2, "drop" -> (SeqOArrayFun8(Ocamlarray.drop))
  | 2, "map" -> (SeqOArrayFun9(Ocamlarray.map))
  | 2, "any" -> (SeqOArrayFun10(Ocamlarray.any))
  | 2, "seqall" -> (SeqOArrayFun10(Ocamlarray.all))
  | 2, "find" -> (SeqOArrayFun11(Ocamlarray.find))
  | 2, "filter" -> (SeqOArrayFun12(Ocamlarray.filter))
  | 2, "foldr" -> (SeqOArrayFun13(Ocamlarray.foldr))
  | 2, "foldl" -> (SeqOArrayFun13(Ocamlarray.foldl))
  | 2, "copy" -> (SeqOArrayFun6(Ocamlarray.copy))
  | 3, "is_empty" -> (SeqOQueueFun4(Ocamlqueue.is_empty))
  | 3, "first" -> (SeqOQueueFun5(Ocamlqueue.first))
  | 3, "last" -> (SeqOQueueFun5(Ocamlqueue.last))
  | 3, "push" -> (SeqOQueueFun3(Ocamlqueue.push))
  | 3, "pop" -> (SeqOQueueFun6(Ocamlqueue.pop))
  | 3, "length" -> (SeqOQueueFun2(Ocamlqueue.length))
  | 3, "nth" -> (SeqOQueueFun7(Ocamlqueue.nth))
  | 3, "append" -> (SeqOQueueFun1(Ocamlqueue.append))
  | 3, "reverse" -> (SeqOQueueFun6(Ocamlqueue.reverse))
  | 3, "push_last" -> (SeqOQueueFun3(Ocamlqueue.push_last))
  | 3, "pop_last" -> (SeqOQueueFun6(Ocamlqueue.pop_last))
  | 3, "take" -> (SeqOQueueFun8(Ocamlqueue.take))
  | 3, "drop" -> (SeqOQueueFun8(Ocamlqueue.drop))
  | 3, "map" -> (SeqOQueueFun9(Ocamlqueue.map))
  | 3, "any" -> (SeqOQueueFun10(Ocamlqueue.any))
  | 3, "seqall" -> (SeqOQueueFun10(Ocamlqueue.all))
  | 3, "find" -> (SeqOQueueFun11(Ocamlqueue.find))
  | 3, "filter" -> (SeqOQueueFun12(Ocamlqueue.filter))
  | 3, "foldr" -> (SeqOQueueFun13(Ocamlqueue.foldr))
  | 3, "foldl" -> (SeqOQueueFun13(Ocamlqueue.foldl))
  | 3, "copy" -> (SeqOQueueFun6(Ocamlqueue.copy))
  | 4, "is_empty" -> (SeqOStackFun4(Ocamlstack.is_empty))
  | 4, "first" -> (SeqOStackFun5(Ocamlstack.first))
  | 4, "last" -> (SeqOStackFun5(Ocamlstack.last))
  | 4, "push" -> (SeqOStackFun3(Ocamlstack.push))
  | 4, "pop" -> (SeqOStackFun6(Ocamlstack.pop))
  | 4, "length" -> (SeqOStackFun2(Ocamlstack.length))
  | 4, "nth" -> (SeqOStackFun7(Ocamlstack.nth))
  | 4, "append" -> (SeqOStackFun1(Ocamlstack.append))
  | 4, "reverse" -> (SeqOStackFun6(Ocamlstack.reverse))
  | 4, "push_last" -> (SeqOStackFun3(Ocamlstack.push_last))
  | 4, "pop_last" -> (SeqOStackFun6(Ocamlstack.pop_last))
  | 4, "take" -> (SeqOStackFun8(Ocamlstack.take))
  | 4, "drop" -> (SeqOStackFun8(Ocamlstack.drop))
  | 4, "map" -> (SeqOStackFun9(Ocamlstack.map))
  | 4, "any" -> (SeqOStackFun10(Ocamlstack.any))
  | 4, "seqall" -> (SeqOStackFun10(Ocamlstack.all))
  | 4, "find" -> (SeqOStackFun11(Ocamlstack.find))
  | 4, "filter" -> (SeqOStackFun12(Ocamlstack.filter))
  | 4, "foldr" -> (SeqOStackFun13(Ocamlstack.foldr))
  | 4, "foldl" -> (SeqOStackFun13(Ocamlstack.foldl))
  | 4, "copy" -> (SeqOStackFun6(Ocamlstack.copy))
  | 5, "is_empty" -> (SeqFinTreeFun4(Fingertree.is_empty))
  | 5, "first" -> (SeqFinTreeFun5(Fingertree.first))
  | 5, "last" -> (SeqFinTreeFun5(Fingertree.last))
  | 5, "push" -> (SeqFinTreeFun3(Fingertree.push))
  | 5, "pop" -> (SeqFinTreeFun6(Fingertree.pop))
  | 5, "length" -> (SeqFinTreeFun2(Fingertree.length))
  | 5, "nth" -> (SeqFinTreeFun7(Fingertree.nth))
  | 5, "append" -> (SeqFinTreeFun1(Fingertree.append))
  | 5, "reverse" -> (SeqFinTreeFun6(Fingertree.reverse))
  | 5, "push_last" -> (SeqFinTreeFun3(Fingertree.push_last))
  | 5, "pop_last" -> (SeqFinTreeFun6(Fingertree.pop_last))
  | 5, "take" -> (SeqFinTreeFun8(Fingertree.take))
  | 5, "drop" -> (SeqFinTreeFun8(Fingertree.drop))
  | 5, "map" -> (SeqFinTreeFun9(Fingertree.map))
  | 5, "any" -> (SeqFinTreeFun10(Fingertree.any))
  | 5, "seqall" -> (SeqFinTreeFun10(Fingertree.all))
  | 5, "find" -> (SeqFinTreeFun11(Fingertree.find))
  | 5, "filter" -> (SeqFinTreeFun12(Fingertree.filter))
  | 5, "foldr" -> (SeqFinTreeFun13(Fingertree.foldr))
  | 5, "foldl" -> (SeqFinTreeFun13(Fingertree.foldl))
  | 5, "copy" -> (SeqFinTreeFun6(Fingertree.copy))
  | _ -> failwith "Method not yet implemented1"

let get_seq_from_list ds_choice l =
  match ds_choice with
  | 0 -> SeqList(Linkedlist.from_list l)
  | 1 -> SeqQueue(Okasakiqueue.from_list l)
  | 2 -> SeqOArray(Ocamlarray.from_list l)
  | 3 -> SeqOQueue(Ocamlqueue.from_list l)
  | 4 -> SeqOStack(Ocamlstack.from_list l)
  | 5 -> SeqFinTree(Fingertree.from_list l)
  | _ -> failwith "Data structure implementation not implemented"

(*Updates AST with data structure choices. This means updating the corresponding field in TmSeqs and TmSeqMethods, getting the correct function implementation in TmSeqMethods and creating the sequence from the term list in TmSeqs.*)
let rec update_ast_w_sel_dss ast sel_dss in_fix =
  let rec update_ast_list_w_sel_dss ast_l sel_dss' l_in_fix =
    (match ast_l with
     | [] -> []
     | hd::tl ->
       let upd_hd = update_ast_w_sel_dss hd sel_dss' l_in_fix in
       upd_hd::(update_ast_list_w_sel_dss tl sel_dss' l_in_fix)) in
  match ast with
  | TmSeq(ti,ty_ident,tm_l,tm_seq,ds_choice) ->
    let upd_tml = update_ast_list_w_sel_dss (get_list_from_tmlist tm_l) sel_dss in_fix in
    let upd_ds_choice = List.assoc ast sel_dss in
    let upd_tm_seq = get_seq_from_list upd_ds_choice upd_tml in
    TmSeq(ti,ty_ident,TmList([]),upd_tm_seq,upd_ds_choice)
  | TmSeqMethod(ti,fun_name,actual_fun,args,arg_index,ds_choice,seqm_in_fix) ->
    let upd_seqm = TmSeqMethod(ti,fun_name,actual_fun,args,arg_index,ds_choice,in_fix) in
    let upd_ds_choice = List.assoc upd_seqm sel_dss in
    let upd_actual_fun = get_actual_fun_w_sel_ds fun_name upd_ds_choice in
    TmSeqMethod(ti,fun_name,upd_actual_fun,args,arg_index,upd_ds_choice,in_fix)
  | TmNop | TmVar _ | TmChar _ | TmFix _ | TmConst _ -> ast
  | TmLam(ti,x,ty,tm) ->
    let upd_tm = update_ast_w_sel_dss tm sel_dss in_fix in
    TmLam(ti,x,ty,upd_tm)
  | TmClos(ti,x,ty,tm,env,pm) ->
    let upd_tm = update_ast_w_sel_dss tm sel_dss in_fix in
    TmClos(ti,x,ty,upd_tm,env,pm)
  | TmApp(ti,tm1,tm2) ->
    let app_in_fix =
      (match tm1 with
       | TmFix _ -> true
       | _ -> in_fix
      ) in
    let upd_tm1 = update_ast_w_sel_dss tm1 sel_dss app_in_fix in
    let upd_tm2 = update_ast_w_sel_dss tm2 sel_dss app_in_fix in
    TmApp(ti,upd_tm1,upd_tm2)
  | TmUtest(ti,tm1,tm2,tm3) ->
    let upd_tm1 = update_ast_w_sel_dss tm1 sel_dss in_fix in
    let upd_tm2 = update_ast_w_sel_dss tm2 sel_dss in_fix in
    let upd_tm3 = update_ast_w_sel_dss tm3 sel_dss in_fix in
    TmUtest(ti,upd_tm1,upd_tm2,upd_tm3)
  | TmIfexp(ti,tm1,tm2,tm3) ->
    let upd_tm1 = update_ast_w_sel_dss tm1 sel_dss in_fix in
    let upd_tm2 = update_ast_w_sel_dss tm2 sel_dss in_fix in
    let upd_tm3 = update_ast_w_sel_dss tm3 sel_dss in_fix in
    TmIfexp(ti,upd_tm1,upd_tm2,upd_tm3)
  | TmMatch _ | TmUC _ | TmTyApp _ | TmTyLam _ ->
    failwith "Not implemented2"

let rec write_test1 n =
  match n > 1000 with
  | true -> false
  | _ ->
    let _ = Printf.printf "let q%d = seqmethod.push_last [Int] q%d 1 \n" (n) (n-1) in
    let _ = Printf.printf "let q%d = seqmethod.push_last [Int] q%d 1 \n" (n+1) (n) in
    let _ = Printf.printf "let q%d = seqmethod.push_last [Int] q%d 1 \n" (n+2) (n+1) in
    let _ = Printf.printf "let q%d = seqmethod.push_last [Int] q%d 1 \n" (n+3) (n+2) in
    let _ = Printf.printf "let q%d = seqmethod.push_last [Int] q%d 1 \n" (n+4) (n+3) in
    let _ = Printf.printf "let q%d = seqmethod.push_last [Int] q%d 1 \n" (n+5) (n+4) in
    let _ = Printf.printf "let q%d = seqmethod.pop [Int] q%d \n" (n+6) (n+5) in
    let _ = Printf.printf "let q%d = seqmethod.pop [Int] q%d \n" (n+7) (n+6) in
    let _ = Printf.printf "let q%d = seqmethod.pop [Int] q%d \n" (n+8) (n+7) in
    let _ = Printf.printf "let q%d = seqmethod.pop [Int] q%d \n" (n+9) (n+8) in
    let _ = Printf.printf "let q%d = seqmethod.pop [Int] q%d \n" (n+10) (n+9) in
    write_test1 (n+11)

let process_ast ast =
  (*let _ = Printf.printf "\nThe complete program is:\n%s\n" (Ustring.to_utf8 (Pprint.pprint false ast)) in*)
  (*-Pre-processing-*)
  (*Find all terms of sequence type and sequence methods, and their internal relationships*)
  let (rls,seqs) = find_rels_and_seqs_in_ast ast [] [] false in
  let rels0 = find_lam_var_rels seqs rls seqs in
  let rels = List.append rels0 (find_vars_with_the_same_name seqs) in
  (*let _ = Printf.printf "The seqs:\n%s\n" (get_tm_list_string seqs) in
  let _ = Printf.printf "The rels:\n%s\n" (get_tm_pair_list_string rels) in*)
  (*Get the sequence constructors*) (*TODO: Remove this step?*)
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
  let mf_matrix2 = Frequencies.translate_mf_assoc_list mf_matrix1 (Sequenceinfo.get_seq_fun_names) in
  (*let _ = Printf.printf "The second version of the mf matrix:\n%s\n" (get_mf_freq_string mf_matrix2) in*)
  (*-Data structure selection algorithm-*)
  let selected_dss = Dssa.main mf_matrix2 in
  (*let _ = Printf.printf "The selected data structures are:\n%s\n" (get_selected_datastructures_string selected_dss) in*)
  (*-Post-processing-*)
  (*Connect selected data structure with all seqs*)
  let sel_dss_assoc_l = connect_seqs_w_sel_dss selected_dss rels_assoc_l3 in
  (*let _ = Printf.printf "The seqs with selected data structures are:\n%s\n" (get_seqs_w_selected_dss_string sel_dss_assoc_l) in*)
  (*Update ast with selected data structures*)
  let upd_ast = update_ast_w_sel_dss ast sel_dss_assoc_l false in
  (*let _ = Printf.printf "The updated ast is:\n%s\n" (Ustring.to_utf8 (Pprint.pprint false upd_ast)) in*)
  upd_ast
