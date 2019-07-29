open Ast
open Dssa
open Linkedlist
open Ustring.Op

let check_if_seq ti =
  match ti with
  | {ety} ->
    (match ety with
     | Some(TySeq _) -> true
     | Some(TySeqMethod(_,(TySeq _))) -> true (*seqmethod that returns a sequence*)
     | Some(TyArrow(_,(TySeq _),_)) -> true (*"let x = s" where s is a sequence*)
     | Some(TyArrow(_,(TySeqMethod(_,(TySeq _))),_)) -> true (*"let x = sm" where sm is a sequence method that returns a sequence*)
     | _ -> false
    )
  | _ -> failwith "Not implemented"

let rec find_rels_in_tmapp tm1 tm2 rels =
  (*!TODO: Some cases below are duplicates if we don't want to distinguish between input and return types of methods*)
  match tm1, tm2, (check_if_seq (Ast.tm_tinfo tm1)), (check_if_seq (Ast.tm_tinfo tm2)), Typesys.getType tm1 with
  | TmLam(lam_ti,_,_,_), TmSeq(seq_ti,_,_,_), true, true, _ (*"let x = new sequence"*) ->
    (*Rel: s1 = s2*)
    let new_rel = (tm1,tm2) in
    new_rel::rels
  | TmLam(lam_ti,_,_,_), TmApp(app_ti,_,_), true, true, _ (*"let x = a1 a2" where application (a1 a2) is of type sequence*) ->
    (*Rel: s1 = s2*)
    let new_rel = (tm1,tm2) in
    new_rel::rels
  | TmLam(lam_ti,_,_,_), TmVar(var_ti,_,_,_), true, true, _ (*"let x = y" where y is of type sequence*) ->
    (*Rel: s1 = s2*)
    let new_rel = (tm1,tm2) in
    new_rel::rels
  | TmVar(var_ti,_,_,_), TmSeq(seq_ti,_,_,_), _, true, TySeqMethod(TySeq(_,_),_) (*"var sequence" where var is a seqmethod and the sequence is the first sequence argument to the method and hence the sequence decides the method's sequence INPUT - and maybe RETURN - type*) ->
    let new_rel = (tm1,tm2) in
    new_rel::rels
  | TmSeqMethod(seqm_ti,_,_,_,_), TmSeq(seq_ti,_,_,_), _, true, TySeqMethod(_,TySeq _) (*"seqmethod sequence" where the sequence is the first sequence argument to the method and hence the sequence decides the method's sequence INPUT and RETURN type*) ->
    (*Rel: return and input type of s1 = s2*)
    let new_rel = (tm1,tm2) in
    new_rel::rels
  | TmSeqMethod(seqm_ti,_,_,_,_), _, _, true, TySeqMethod(_,TySeq _) (*"seqmethod a" where a is the first argument of type sequence to the method and hence a decides the method's sequence INPUT and RETURN type*) ->
    (*Rel: return and input type of s1 = s2*)
    let new_rel = (tm1,tm2) in
    new_rel::rels
  | TmSeqMethod(seqm_ti,_,_,_,_), TmSeq(seq_ti,_,_,_), _, true, TySeqMethod _ (*"seqmethod sequence" where the sequence is the first sequence argument to the method and hence the sequence decides the method's sequence INPUT type, but not the return type since the return type of the method is not a sequence*) ->
    (*Rel: input type of s1 = s2*)
    let new_rel = (tm1,tm2) in
    new_rel::rels
  | TmSeqMethod(seqm_ti,_,_,_,_), _, _, true, TySeqMethod _ (*"seqmethod a" where a is the first argument of type sequence to the method and hence a decides the method's sequence INPUT type, but not the return type since the return type of the method is not a sequence*) ->
    (*Rel: input type of s1 = s2*)
    let new_rel = (tm1,tm2) in
    new_rel::rels
  | TmApp(app_ti,TmSeqMethod(seqm_ti,fun_name,actual_fun,args,arg_index),TmLam(lam_ti,x,lam_ty,lam_tm)), TmSeq(seq_ti,_,_,_), _, true, _ ->
    find_rels_in_tmapp (TmSeqMethod(seqm_ti,fun_name,actual_fun,args,arg_index)) tm2 rels
  | TmApp(app_ti,_,_), TmSeq(seq_ti,_,_,_), _, true, TySeqMethod _ (*"a1 sequence" where a1 is of type sequence method and sequence is an argument (but not the first) to it. The method will already have the sequence type set from its first argument, so its sequence type will decide the sequence type of the sequence.*) ->
    (*Rel: s2 = input type of s1*)
    let new_rel = (tm2,tm1) in
    new_rel::rels
  | TmApp(app_ti,_,_), _, _, true, TySeqMethod _ (*"a1 a2" where a1 is of type sequence method and a2 is of type sequence. The method will already have the sequence type set from its first argument, so its sequence type will decide the sequence type of a2.*) ->
    (*Rel: s2 = input type of s1*)
    let new_rel = (tm2,tm1) in
    new_rel::rels
  | _ ->
    rels

let print_seq_ty ti =
  match ti with
  | {ety} ->
    (match ety with
     | Some(TySeq(seq_ty,_)) ->
       let _ = Printf.printf "The sequence's element type is: %s\n" (Ustring.to_utf8 (Pprint.pprint_ty seq_ty)) in
       true
     | _ -> false)
  | _ -> false

let rec find_sequences_in_ast t rels seqs =
  let rec find_sequences_in_ast_list l l_rels l_seqs =
    (match l with
     | [] -> (l_rels,l_seqs)
     | hd::tl ->
       let (new_l_rels,new_l_seqs) = find_sequences_in_ast hd l_rels l_seqs in
       find_sequences_in_ast_list tl new_l_rels new_l_seqs
    ) in
  match t with
  | TmSeq(ti,ty_ident,tm_l,tm_seq) ->
    let new_seqs = t::seqs in
    find_sequences_in_ast_list (get_list_from_tm_list tm_l) rels new_seqs
  | TmNop ->
    (rels,seqs)
  | TmVar(ti,_,_,_) | TmChar(ti,_) | TmSeqMethod(ti,_,_,_,_) | TmFix(ti) | TmConst(ti,_) ->
    if check_if_seq ti then
      (rels,t::seqs)
    else
      (rels,seqs)
  | TmLam(ti,_,_,tm) | TmClos(ti,_,_,tm,_,_) ->
    let (new_rels,new_seqs) =
      (if check_if_seq ti then
         (rels,t::seqs)
       else
         (rels,seqs)
      ) in
    find_sequences_in_ast tm new_rels new_seqs
  | TmApp(ti,tm1,tm2) ->
    let new_rels1 = find_rels_in_tmapp tm1 tm2 rels in
    let (new_rels2,new_seqs1) = find_sequences_in_ast tm1 new_rels1 seqs in
    find_sequences_in_ast tm2 new_rels2 new_seqs1
  | TmUtest(ti,tm1,tm2,tm3) | TmIfexp(ti,tm1,tm2,tm3) ->
    let (new_rels1,new_seqs1) =
      (if check_if_seq ti then
         (rels,t::seqs)
       else
         (rels,seqs)
      ) in
    let (new_rels2,new_seqs2) = find_sequences_in_ast tm1 new_rels1 new_seqs1 in
    let (new_rels3,new_seqs3) = find_sequences_in_ast tm2 new_rels2 new_seqs2 in
    find_sequences_in_ast tm3 new_rels3 new_seqs3
  | TmMatch _ | TmUC _ | TmTyApp _ | TmTyLam _ ->
    failwith "Not implemented"

let rec get_sequence_constructors seqs =
  match seqs with
  | [] -> []
  | hd::tl ->
    (match hd with
     | TmSeq _ -> hd::(get_sequence_constructors tl)
     | _ -> get_sequence_constructors tl
    )

let rec init_assoc_list l =
  match l with
  | [] -> []
  | hd::tl ->
    (hd,[])::(init_assoc_list tl)

let check_if_key_exists key assoc_list =
  if List.mem_assoc key assoc_list then
    assoc_list
  else
    (key,[])::assoc_list

let update_assoc_list_list_entry key new_val assoc_list =
  (*Add key to list if not in list*)
  let upd_assoc_list1 = check_if_key_exists key assoc_list in
  (*Get the entry currently associated with key*)
  let curr_entry = List.assoc key upd_assoc_list1 in
  (*Add new value to current entry*)
  let upd_entry = new_val::curr_entry in
  (*Remove old entry from assoc list*)
  let upd_assoc_list2 = List.remove_assoc key upd_assoc_list1 in
  (*Add updated entry to assoc list*)
  (key,upd_entry)::upd_assoc_list2

let rec reduce_relationships rels rels_assoc_list =
  match rels with
  | [] -> rels_assoc_list
  | (hd1,hd2)::tl ->
    (*Add hd1 to list if not in list*)
    let upd_rels_assoc_list1 = check_if_key_exists hd1 rels_assoc_list in
    (*Add relationship hd2->hd1 to assoc list*)
    let upd_rels_assoc_list2 = update_assoc_list_list_entry hd2 hd1 upd_rels_assoc_list1 in
    reduce_relationships tl upd_rels_assoc_list2

let rec find_all_related seqs rels_assoc_list new_rels =
  match seqs, new_rels with
  | [], [] -> []
  | [], _ -> find_all_related new_rels rels_assoc_list []
  | (hd::tl), _ ->
    let hd_rels = List.assoc hd rels_assoc_list in
    let upd_new_rels = List.append hd_rels new_rels in
    hd::(find_all_related tl rels_assoc_list upd_new_rels)

let rec get_seq_cons_relationships seq_cons rels_assoc_list new_rels_assoc_list =
  match seq_cons with
  | [] -> new_rels_assoc_list
  | hd::tl ->
    let hd_rels = List.assoc hd rels_assoc_list in
    let hd_all_rels = find_all_related hd_rels rels_assoc_list [] in
    let upd_new_rels_assoc_list = (hd,hd_all_rels)::new_rels_assoc_list in
    get_seq_cons_relationships tl rels_assoc_list upd_new_rels_assoc_list

let rec init_seqmethod_assoc_list_helper fun_names =
  match fun_names with
  | [] -> []
  | hd::tl ->
    (hd,0)::(init_seqmethod_assoc_list_helper tl)

let get_fun_names =
(*!TODO: Collect this from file*)
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
   "map"]

let init_seqmethod_assoc_list =
  let fun_names = get_fun_names in
  init_seqmethod_assoc_list_helper fun_names

let rec get_sequence_methods seqs =
  match seqs with
  | [] -> []
  | hd::tl ->
    (match hd with
     | TmSeqMethod _ ->
       hd::(get_sequence_methods tl)
     | _ -> get_sequence_methods tl
    )

let get_fun_name_from_seqmethod seqm =
  match seqm with
  | TmSeqMethod(_,fun_name,_,_,_) -> (Ustring.to_utf8 fun_name)
  | _ -> failwith "We cannot get a fun name from this term type"

let rec create_mf_matrix_row seqm_assoc_list seqmethods =
  match seqmethods with
  | [] ->
    let _ = Printf.printf "%s\n" "Empty seqmethod list" in
    seqm_assoc_list
  | hd::tl ->
    let fun_name = get_fun_name_from_seqmethod hd in
    let curr_fun_count = List.assoc fun_name seqm_assoc_list in
    let upd_seqm_assoc_list1 = List.remove_assoc fun_name seqm_assoc_list in
    let upd_seqm_assoc_list2 = (fun_name,(curr_fun_count+1))::upd_seqm_assoc_list1 in
    create_mf_matrix_row upd_seqm_assoc_list2 tl

let rec get_sequence_method_counts rels_assoc_list =
  match rels_assoc_list with
  | [] -> []
  | (hd,hdl)::tl ->
    let seqmethod_assoc_list = init_seqmethod_assoc_list in
    let hd_seqmethods = get_sequence_methods hdl in
    let mf_matrix_row = create_mf_matrix_row seqmethod_assoc_list hd_seqmethods in
    mf_matrix_row::(get_sequence_method_counts tl)

let rec init_selected_list_assoc list_assoc =
  match list_assoc with
  | [] -> []
  | (hd1,_)::tl ->
    (hd1,-1)::(init_selected_list_assoc tl)

let rec set_seq_choices selected_ds_assoc_list seq_group ds_choice =
  match seq_group with
  | [] -> selected_ds_assoc_list
  | hd::tl ->
    let upd_selected_ds_assoc_list1 = List.remove_assoc hd selected_ds_assoc_list in
    let upd_selected_ds_assoc_list2 = (hd,ds_choice)::upd_selected_ds_assoc_list1 in
    set_seq_choices upd_selected_ds_assoc_list2 tl ds_choice

let rec link_seqs_to_selected_ds selected_data_structures rels_assoc_list selected_ds_assoc_list =
  match selected_data_structures, rels_assoc_list with
  | [], [] -> selected_ds_assoc_list
  | [], _ | _, [] -> failwith "The lists should have the same length"
  | hd1::tl1, (hd2,hdl2)::tl2 ->
    let top_choice =
      (match hd1 with
       | [] -> failwith "We have no data structure choices"
       | hd3::tl3 -> hd3
      ) in
    let seq_group = hd2::hdl2 in
    let upd_selected_ds_assoc_list = set_seq_choices selected_ds_assoc_list seq_group top_choice in
    link_seqs_to_selected_ds tl1 tl2 upd_selected_ds_assoc_list
  | _ -> failwith "Not implemented"

let update_ti ti ds_choice =
  let fi' =
    (match ti with
     | {fi} -> fi
    ) in
  let ty' =
    (match ti with
     | {ety} ->
       (match ety with
        | Some(TySeq(ty,ds_choice1)) (*!TODO: dschoice in ty?*) ->
          Some(TySeq(ty,ds_choice))
        | Some(TySeqMethod(TySeq(ty1,ds_choice1),TySeq(ty2,ds_choice2))) ->
          Some(TySeqMethod(TySeq(ty1,ds_choice),TySeq(ty2,ds_choice)))
        | Some(TySeqMethod(TySeq(ty1,ds_choice1),ret_ty)) ->
          Some(TySeqMethod(TySeq(ty1,ds_choice),ret_ty))
        | Some(TySeqMethod(inp_ty,TySeq(ty2,ds_choice2))) ->
          Some(TySeqMethod(inp_ty,TySeq(ty2,ds_choice)))
        | Some(TyArrow(fi,TySeq(ty,ds_choice1), b_ty)) ->
          Some(TyArrow(fi,TySeq(ty,ds_choice), b_ty))
        | Some(TyArrow(fi,TySeqMethod(TySeq(ty1,ds_choice1),TySeq(ty2,ds_choice2)), b_ty)) ->
          Some(TyArrow(fi,TySeqMethod(TySeq(ty1,ds_choice),TySeq(ty2,ds_choice)), b_ty))
        | Some(TyArrow(fi,TySeqMethod(TySeq(ty1,ds_choice1),ret_ty), b_ty)) ->
          Some(TyArrow(fi,TySeqMethod(TySeq(ty1,ds_choice),ret_ty), b_ty))
        | Some(TyArrow(fi,TySeqMethod(inp_ty, TySeq(ty1,ds_choice1)), b_ty)) ->
          Some(TyArrow(fi,TySeqMethod(inp_ty,TySeq(ty1,ds_choice)), b_ty))
        | _ -> failwith "It is not of the right type"
       )
    ) in
  {ety=ty';fi=fi'}

let get_actual_fun ds_choice fun_name =
  match ds_choice, (Ustring.to_utf8 fun_name) with
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
  | _ -> failwith "Method not yet implemented1"

let rec update_ast_with_choices t selected_ds_assoc_list =
  let rec update_ast_list_with_choices l l_selected_ds_assoc_list =
    (match l with
     | [] -> []
     | hd::tl ->
       let upd_hd = update_ast_with_choices hd l_selected_ds_assoc_list in
       update_ast_list_with_choices tl l_selected_ds_assoc_list
    ) in
  match t with
  | TmSeq(ti,ty_ident,tm_l,tm_seq) ->
    let upd_tm_l = update_ast_list_with_choices (get_list_from_tm_list tm_l) selected_ds_assoc_list in
    let ds_choice = List.assoc t selected_ds_assoc_list in
    let upd_ti = update_ti ti ds_choice in
    TmSeq(upd_ti,ty_ident,TmList(upd_tm_l),tm_seq)
  | TmNop ->
    t
  | TmVar(ti,a,b,c) ->
    if check_if_seq ti then
      let ds_choice = List.assoc t selected_ds_assoc_list in
      let upd_ti = update_ti ti ds_choice in
      TmVar(upd_ti,a,b,c)
    else
      t
  | TmChar(ti,a) ->
    if check_if_seq ti then
      let ds_choice = List.assoc t selected_ds_assoc_list in
      let upd_ti = update_ti ti ds_choice in
      TmChar(upd_ti,a)
    else
      t
  | TmSeqMethod(ti,fun_name,actual_fun,c,d) ->
    let ds_choice = List.assoc t selected_ds_assoc_list in
    let upd_ti = update_ti ti ds_choice in
    let upd_actual_fun = get_actual_fun ds_choice fun_name in
    TmSeqMethod(upd_ti,fun_name,upd_actual_fun,c,d)
  | TmFix(ti) ->
    if check_if_seq ti then
      let ds_choice = List.assoc t selected_ds_assoc_list in
      let upd_ti = update_ti ti ds_choice in
      TmFix(upd_ti)
    else
      t
  | TmConst(ti,a) ->
    if check_if_seq ti then
      let ds_choice = List.assoc t selected_ds_assoc_list in
      let upd_ti = update_ti ti ds_choice in
      TmConst(upd_ti,a)
    else
      t
  | TmLam(ti,a,b,tm) ->
    let upd_tm = update_ast_with_choices tm selected_ds_assoc_list in
    if check_if_seq ti then
      let ds_choice = List.assoc t selected_ds_assoc_list in
      let upd_ti = update_ti ti ds_choice in
      TmLam(upd_ti,a,b,upd_tm)
    else
      TmLam(ti,a,b,upd_tm)
  | TmClos(ti,a,b,tm,c,d) ->
    let upd_tm = update_ast_with_choices tm selected_ds_assoc_list in
    if check_if_seq ti then
      let ds_choice = List.assoc t selected_ds_assoc_list in
      let upd_ti = update_ti ti ds_choice in
      TmClos(upd_ti,a,b,upd_tm,c,d)
    else
      TmClos(ti,a,b,upd_tm,c,d)
  | TmApp(ti,tm1,tm2) ->
    let upd_tm1 = update_ast_with_choices tm1 selected_ds_assoc_list in
    let upd_tm2 = update_ast_with_choices tm2 selected_ds_assoc_list in
    let res =
      (match tm1,tm2 with
       | TmSeqMethod _, TmSeq _ -> true
       | _ -> false
      ) in
    if res && (check_if_seq ti) && (List.mem_assoc t selected_ds_assoc_list) then
      let ds_choice = List.assoc t selected_ds_assoc_list in
      let upd_ti = update_ti ti ds_choice in
      TmApp(upd_ti,upd_tm1,upd_tm2)
    else
      TmApp(ti,upd_tm1,upd_tm2)
  | TmUtest(ti,tm1,tm2,tm3) ->
    let upd_tm1 = update_ast_with_choices tm1 selected_ds_assoc_list in
    let upd_tm2 = update_ast_with_choices tm2 selected_ds_assoc_list in
    let upd_tm3 = update_ast_with_choices tm3 selected_ds_assoc_list in
    if check_if_seq ti then
      let ds_choice = List.assoc t selected_ds_assoc_list in
      let upd_ti = update_ti ti ds_choice in
      TmUtest(upd_ti,upd_tm1,upd_tm2,upd_tm3)
    else
      TmUtest(ti,upd_tm1,upd_tm2,upd_tm3)
  | TmIfexp(ti,tm1,tm2,tm3) ->
    let upd_tm1 = update_ast_with_choices tm1 selected_ds_assoc_list in
    let upd_tm2 = update_ast_with_choices tm2 selected_ds_assoc_list in
    let upd_tm3 = update_ast_with_choices tm3 selected_ds_assoc_list in
    if check_if_seq ti then
      let ds_choice = List.assoc t selected_ds_assoc_list in
      let upd_ti = update_ti ti ds_choice in
      TmIfexp(upd_ti,upd_tm1,upd_tm2,upd_tm3)
    else
      TmIfexp(ti,upd_tm1,upd_tm2,upd_tm3)
  | TmMatch _ | TmUC _ | TmTyApp _ | TmTyLam _ ->
    failwith "Not implemented"

let rec build_fake_selected_ds size =
  match size with
  | 0 -> []
  | _ ->
    [0]::(build_fake_selected_ds (size-1))

let process_ast t =
  let _ = Printf.printf "The program is:\n%s\n" (Ustring.to_utf8 (Pprint.pprint true t)) in
  (*Find all terms of sequence type and their internal relationships*)
  let (rels,seqs) = find_sequences_in_ast t [] [] in
  (*Get the sequence constructors from the list of sequences*)
  let seq_cons = get_sequence_constructors seqs in
  (*Init association list for relationships*)
  let rels_assoc_list1 = init_assoc_list seqs in
  (*Reduce relationships from rels*)
  let rels_assoc_list2 = reduce_relationships rels rels_assoc_list1 in
  (*Create an assoc list that links sequence constructors to relationships*)
  let rels_assoc_list3 = get_seq_cons_relationships seq_cons rels_assoc_list2 [] in
  (*Create the method frequency matrix from reduced relationships assoc lis*)
  let mf_matrix1 = get_sequence_method_counts rels_assoc_list3 in
  (*Translate mf matrix with counts to frequencies*)
  let mf_matrix2 = Frequencies.translate_mf_assoc_list mf_matrix1 get_fun_names in
  (*!TODO: Keep track of order of sequences*)
  (*Call algorithm*)
  (*!TODO:let selected_data_structures = Dssa.main mf_matrix2 in*)
  let selected_data_structures = build_fake_selected_ds (List.length mf_matrix2) in
  (*Init assoc list for selected data structures*)
  let selected_list_assoc1 = init_selected_list_assoc rels_assoc_list2 in
  let selected_list_assoc2 = link_seqs_to_selected_ds selected_data_structures rels_assoc_list3 selected_list_assoc1 in
  let t' = update_ast_with_choices t selected_list_assoc2 in
  t'

(*Test section*)
let print_test_res test_name test_res =
  if test_res then
    "Test " ^ test_name ^ " passed!"
  else
    "Test " ^ test_name ^ " failed!"

let test_check_if_seq =
  let ti1 = {ety=Some(TySeq(TyDyn,0));fi=NoInfo} in
  let test1 = (true = (check_if_seq ti1)) in
  let ti2 = {ety=Some(TySeqMethod(TyDyn,TySeq(TyDyn,0)));fi=NoInfo} in
  let test2 = (true = (check_if_seq ti2)) in
  let ti3 = {ety=Some(TyArrow(NoInfo,TySeq(TyDyn,0),TyDyn));fi=NoInfo} in
  let test3 = (true = (check_if_seq ti3)) in
  let ti4 = {ety=Some(TyArrow(NoInfo,TySeqMethod(TyDyn,TySeq(TyDyn,0)),TyDyn));fi=NoInfo} in
  let test4 = (true = (check_if_seq ti4)) in
  let _ = Printf.printf "%s\n" (print_test_res "check_if_seq" (test1 && test2 && test3 && test4)) in
  true

let get_ty_seq_int_noinfo =
  TySeq(TyGround(NoInfo,GInt),-1)

let get_ty_void_noinfo =
  TyGround(NoInfo,GVoid)

let create_dummy_fi dummy_filename =
  Msg.Info(dummy_filename,0,0,0,0)

let create_dummy_ti dummy_ety dummy_fi =
  {ety=Some(dummy_ety);fi=dummy_fi}

let create_tmconst_int dummy_filename n =
  TmConst(
    (create_dummy_ti (TyGround(NoInfo,GInt)) (create_dummy_fi dummy_filename)),
    CInt(n)
  )

let rec compare_relationships rels1 rels2 =
  match rels1, rels2 with
  | [], [] -> true
  | [], _ -> false
  | _, [] -> false
  | (hd11,hd12)::tl1, (hd21,hd22)::tl2 ->
    if (hd11 = hd21) && (hd12 == hd22) then
      compare_relationships tl1 tl2
    else
      false
  | _ -> failwith "Unexpected format of rels list"

let rec compare_sequences seq1 seq2 =
  match seq1, seq2 with
  | [], [] -> true
  | [], _ -> false
  | _, [] -> false
  | hd1::tl1, hd2::tl2 ->
    if hd1 = hd2 then
      compare_sequences tl1 tl2
    else
      false

let rec compare_assoc_list_of_lists l1 l2 =
  match l1, l2 with
  | [], [] -> true
  | [], _ -> false
  | _, [] -> false
  | (hd1,hdl1)::tl1, (hd2,hdl2)::tl2 ->
    if (hd1 == hd2) && (compare_sequences hdl1 hdl2) then
      compare_assoc_list_of_lists tl1 tl2
    else
      false
  | _ -> failwith "Unexpected form of assoc list of lists"

let rec compare_relationships_lists l1 l2 =
  match l1, l2 with
  | [], [] -> true
  | [], _ -> false
  | _, [] -> false
  | hd1::tl1, hd2::tl2 ->
    if compare_relationships hd1 hd2 then
      compare_relationships_lists tl1 tl2
    else
      let _ = Printf.printf "%d\n" (List.length l1) in
      false
  | _ -> failwith "Unexpected for of mf_matrix first version"

let run_process_test1 =
  (*TEST1*)
  (*let s = newseq [int] (1)*)
  (*TmApp((lam s:Dyn. Nop), TmSeq(1))*)
  let seq1 =
    TmSeq(
      (create_dummy_ti get_ty_seq_int_noinfo (create_dummy_fi (us"seq1_fi1"))),
      us"int",
      TmList(
        [(create_tmconst_int (us"seq1_fi2") 1)]
      ),
      SeqNone
    ) in
  let lam1 =
    TmLam(
      (create_dummy_ti (TyArrow(NoInfo,get_ty_seq_int_noinfo,get_ty_void_noinfo)) (create_dummy_fi (us"lam1_fi1"))),
      us"s",
      TyDyn,
      TmNop
    ) in
  let app1 =
    TmApp(
      (create_dummy_ti get_ty_void_noinfo (create_dummy_fi (us"app1_fi1"))),
      lam1,
      seq1
    ) in
  let ast1 = app1 in
  (*Test find_sequences_in_ast*)
  let (rels,seqs) = find_sequences_in_ast ast1 [] [] in
  let exp_rels = [(lam1,seq1)] in
  let comp_rels_res = compare_relationships rels exp_rels in
  let exp_seqs = [seq1;lam1] in
  let comp_seqs_res = compare_sequences seqs exp_seqs in
  (*Test get_sequence_constructors*)
  let seq_cons = get_sequence_constructors seqs in
  let exp_seq_cons = [seq1] in
  let comp_seq_cons_res = compare_sequences seq_cons exp_seq_cons in
  (*Test init_assoc_list*)
  let rels_assoc_list1 = init_assoc_list seqs in
  let exp_rels_assoc_list1 = [(seq1,[]);(lam1,[])] in
  let comp_rels_assoc_list1_res = compare_assoc_list_of_lists rels_assoc_list1 exp_rels_assoc_list1 in
  (*Test reduce_relationships*)
  let rels_assoc_list2 = reduce_relationships rels rels_assoc_list1 in
  let exp_rels_assoc_list2 = [(seq1,[lam1]);(lam1,[])] in
  let comp_rels_assoc_list2_res = compare_assoc_list_of_lists rels_assoc_list2 exp_rels_assoc_list2 in
  (*Test get_seq_cons_relationships*)
  let rels_assoc_list3 = get_seq_cons_relationships seq_cons rels_assoc_list2 [] in
  let exp_rels_assoc_list3 = [(seq1,[lam1])] in
  let comp_rels_assoc_list3_res = compare_assoc_list_of_lists rels_assoc_list3 exp_rels_assoc_list3 in
  (*Test get_sequence_method_counts*)
  let mf_matrix1 = get_sequence_method_counts rels_assoc_list3 in
  let exp_mf_matrix1 = [[("is_empty",0);
                        ("first",0);
                        ("last",0);
                        ("push",0);
                        ("pop",0);
                        ("length",0);
                        ("nth",0);
                        ("append",0);
                        ("reverse",0);
                        ("push_last",0);
                        ("pop_last",0);
                        ("take",0);
                         ("drop",0);
                         ("map",0);]] in
  let comp_mf_matrix1_res = compare_relationships_lists mf_matrix1 exp_mf_matrix1 in
  (*Test translate_mf_assoc_list*)
  let mf_matrix2 = Frequencies.translate_mf_assoc_list mf_matrix1 get_fun_names in
  let exp_mf_matrix2 = [[Frequencies.Zero;
                        Frequencies.Zero;
                        Frequencies.Zero;
                        Frequencies.Zero;
                        Frequencies.Zero;
                        Frequencies.Zero;
                        Frequencies.Zero;
                        Frequencies.Zero;
                        Frequencies.Zero;
                        Frequencies.Zero;
                        Frequencies.Zero;
                        Frequencies.Zero;
                        Frequencies.Zero;]] in
  let comp_mf_matrix2_res = compare_sequences mf_matrix2 exp_mf_matrix2 in
  let test_res_str = Printf.printf "%s\n" (print_test_res "process_test1" (comp_rels_res && comp_seqs_res && comp_seq_cons_res && comp_rels_assoc_list1_res && comp_rels_assoc_list2_res && comp_rels_assoc_list3_res && comp_mf_matrix1_res && comp_mf_matrix2_res)) in
  true

let run_tests =
  let _ = test_check_if_seq in
  let _ = run_process_test1 in
true
