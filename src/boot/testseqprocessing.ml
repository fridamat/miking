open Ast
open Linkedlist
open Seqprocessing
open Ustring.Op

(*--- Helper methods ---*)
let get_mock_tyseq_int =
  TySeq(TyGround(NoInfo,GInt))

let get_mock_gvoid =
  TyGround(NoInfo,GVoid)

let get_mock_gint =
  TyGround(NoInfo,GInt)

let get_mock_tyarrow_tyseq_int_gvoid =
  TyArrow(NoInfo,
          get_mock_tyseq_int,
          get_mock_gvoid)

let get_mock_tyarrow_gint_gvoid =
  TyArrow(NoInfo,
          get_mock_gint,
          get_mock_gvoid)

let get_mock_tyarrow_tyseq_int_gint =
  TyArrow(NoInfo,
          get_mock_tyseq_int,
          get_mock_gint)

let get_mock_tyarrow_tyseq_int_tyseq_int =
  TyArrow(NoInfo,
          get_mock_tyseq_int,
          get_mock_tyseq_int)

let get_mock_tyarrow_tyseq_int_tyseq_int_tyseq_int =
  TyArrow(NoInfo,
          get_mock_tyseq_int,
          TyArrow(NoInfo,
                  get_mock_tyseq_int,
                  get_mock_tyseq_int))

let create_mock_fi mock_file_name =
  Msg.Info(mock_file_name,0,0,0,0)

let create_mock_ti mock_ety mock_file_name =
  let mock_fi = create_mock_fi mock_file_name in
  {ety=Some(mock_ety);fi=mock_fi}

let create_mock_tmconst_int n mock_file_name =
  TmConst((create_mock_ti (get_mock_gint) mock_file_name),
          CInt(n))

let get_test_res_string res =
  if res then
    "PASSED"
  else
    "FAILED :("

(*--- Comparer methods ---*)
let rec compare_terms t1 t2 =
  let rec compare_term_lists l1 l2 =
    (match l1, l2 with
     | [], [] -> true
     | [], _ | _, [] -> false
     | hd1::tl1, hd2::tl2 ->
       if compare_terms hd1 hd2 then
         compare_term_lists tl1 tl2
       else
         false
     | _ -> false) in
  (*TODO:Method for comparing variables such as x*)
  match t1, t2 with
  | TmChar(_,n1),TmChar(_,n2) -> n1 = n2
  | TmConst(_,c1),TmConst(_,c2) -> c1 = c2
  | TmNop, TmNop -> true
  | TmVar(_,id1,_,_), TmVar(_,id2,_,_) -> id1 = id2
  | TmLam(_,var1,ty1,tm1), TmLam(_,var2,ty2,tm2) ->
    (var1 == var2) && (Typesys.tyequal ty1 ty2) && (compare_terms tm1 tm2)
  | TmClos(_,var1,ty1,tm1,_,_), TmClos(_,var2,ty2,tm2,_,_) ->
    (var1 == var2) && (Typesys.tyequal ty1 ty2) && (compare_terms tm1 tm2)
  | TmApp(_,tm11,tm12), TmApp(_,tm21,tm22) ->
    (compare_terms tm11 tm21) && (compare_terms tm12 tm22)
  | TmIfexp(_,tm11,tm12,tm13), TmIfexp(_,tm21,tm22,tm23) ->
    (compare_terms tm11 tm21) && (compare_terms tm12 tm22) && (compare_terms tm13 tm23)
  | TmFix _, TmFix _ -> true
  | TmSeq(_,_,tm_l1,_,ds_choice1), TmSeq(_,_,tm_l2,_,ds_choice2) ->
    (compare_term_lists (get_list_from_tmlist tm_l1) (get_list_from_tmlist tm_l2)) && (ds_choice1 == ds_choice2)
  | TmSeqMethod(_,fun_name1,_,_,_,ds_choice1), TmSeqMethod(_,fun_name2,_,_,_,ds_choice2) ->
    ((Ustring.to_utf8 fun_name1) = (Ustring.to_utf8 fun_name2)) && (ds_choice1 == ds_choice2) (*TODO: Check actual_fun as well?*)
  | _ -> false

let rec compare_rels rels1 rels2 =
  match rels1, rels2 with
  | [], [] -> true
  | [], _ | _, [] -> false
  | (hd11,hd12)::tl1, (hd21,hd22)::tl2 ->
    if (hd11 == hd21) && (hd12 == hd22) then (*TODO: Comparer method instead, if so method for value of bool or int also needed*)
      compare_rels tl1 tl2
    else
      false

      let rec compare_rels rels1 rels2 =
        match rels1, rels2 with
        | [], [] -> true
        | [], _ | _, [] -> false
        | (hd11,hd12)::tl1, (hd21,hd22)::tl2 ->
          if (hd11 == hd21) && (hd12 == hd22) then (*TODO: Comparer method instead, if so method for value of bool or int also needed*)
            compare_rels tl1 tl2
          else
            false

let rec compare_seqs seqs1 seqs2 =
  match seqs1, seqs2 with
  | [], [] -> true
  | [], _ | _, [] -> false
  | hd1::tl1, hd2::tl2 ->
    if (compare_terms hd1 hd2) then
      compare_seqs tl1 tl2
    else
      false

let rec compare_rels_assoc_list rels_assoc_l1 rels_assoc_l2 =
  match rels_assoc_l1, rels_assoc_l2 with
  | [], [] -> true
  | [], _ | _, [] -> false
  | (hd1,hdl1)::tl1, (hd2,hdl2)::tl2 ->
    if (compare_terms hd1 hd2) && (compare_seqs hdl1 hdl2) then
      compare_rels_assoc_list tl1 tl2
    else
      false

let rec compare_mf_matrix_row row1 row2 =
  match row1, row2 with
  | [], [] -> true
  | [], _ | _, [] -> false
  | (hd11,hd12)::tl1, (hd21,hd22)::tl2 ->
    if (hd11 = hd21) && (hd12 == hd22) then
      compare_mf_matrix_row tl1 tl2
    else false

let rec compare_mf_matrix_count mf_matrix1 mf_matrix2 =
  match mf_matrix1, mf_matrix2 with
  | [], [] -> true
  | [], _ | _, [] -> false
  | hd1::tl1, hd2::tl2 ->
    (compare_mf_matrix_row hd1 hd2) && (compare_mf_matrix_count tl1 tl2)

let compare_asts ast1 ast2 =
  compare_terms ast1 ast2

(*--- Tests ---*)
(*TEST 1: Test all process steps individually
  Program:
    let s = new_seq [int] (1)
  AST:
  TmApp((lam s:Dyn Nop), TmSeq(1))*)
let run_process_steps_test1 =
  let seq1 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"se1_fi1")),
          us"int",
          TmList([(create_mock_tmconst_int 1 (us"seq1_fi2"))]),
          SeqNone,
          -1) in
  let lam1 =
    TmLam((create_mock_ti (get_mock_tyarrow_tyseq_int_gvoid) (us"lam1_fi1")),
          us"s",
          TyDyn,
          TmNop) in
  let app1 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app1_fi1")),
          lam1,
          seq1) in
  let ast = app1 in
  (*Test method "find_rels_and_seqs_in_ast"*)
  let (rels,seqs) = find_rels_and_seqs_in_ast ast [] [] in
  let exp_rels = [(lam1,seq1)] in
  let comp_rels_res = compare_rels rels exp_rels in
  let exp_seqs = [lam1;seq1] in
  let comp_seqs_res = compare_seqs seqs exp_seqs in
  (*Test method "find_seq_cons_among_seqs"*)
  let seq_cons = find_seq_cons_among_seqs seqs in
  let exp_seq_cons = [seq1] in
  let comp_seq_cons_res = compare_seqs seq_cons exp_seq_cons in
  (*Test method "init_rels_assoc_list"*)
  let rels_assoc_l1 = init_rels_assoc_list seqs in
  let exp_rels_assoc_l1 = [(lam1,[]);(seq1,[])] in
  let comp_rels_assoc_l1_res = compare_rels_assoc_list rels_assoc_l1 exp_rels_assoc_l1 in
  (*Test method "transl_rels_to_rels_assoc_list"*)
  let rels_assoc_l2 = transl_rels_to_rels_assoc_list rels rels_assoc_l1 in
  let exp_rels_assoc_l2 = [(seq1,[lam1]);(lam1,[seq1])] in
  let comp_rels_assoc_l2_res = compare_rels_assoc_list rels_assoc_l2 exp_rels_assoc_l2 in
  (*Test method "init_visited_seqs_assoc_list"*)
  let vis_seqs_assoc_l = init_visited_seqs_assoc_list rels_assoc_l2 in
  let exp_vis_seqs_assoc_l = [(seq1,false);(lam1,false)] in
  let comp_vis_seqs_assoc_l_res = compare_rels vis_seqs_assoc_l exp_vis_seqs_assoc_l in
  (*Test method "reduce_rels"*)
  let rels_assoc_l3 = reduce_rels rels_assoc_l2 (init_visited_seqs_assoc_list rels_assoc_l2) in
  let exp_rels_assoc_l3 = [(seq1,[lam1])] in
  let comp_rels_assoc_l3_res = compare_rels_assoc_list rels_assoc_l3 exp_rels_assoc_l3 in
  (*Test method "create_mf_matrix"*)
  let mf_matrix1 = create_mf_matrix rels_assoc_l3 in
  let exp_mf_matrix1 = [init_mf_row] in
  let comp_mf_matrix1_res = compare_mf_matrix_count mf_matrix1 exp_mf_matrix1 in
  (*Run method "Frequencies.translate_mf_assoc_list" - tested in Frequencies*)
  let mf_matrix2 = Frequencies.translate_mf_assoc_list mf_matrix1 in
  (*Mock algorithm step - tested in Dssa*)
  let selected_dss = [[0]] in
  (*Test method "connect_seqs_w_sel_dss"*)
  let sel_dss_assoc_l = connect_seqs_w_sel_dss selected_dss rels_assoc_l3 in
  let exp_sel_dss_assoc_l = [(seq1,0);(lam1,0)] in
  let comp_sel_dss_assoc_l_res = compare_rels sel_dss_assoc_l exp_sel_dss_assoc_l in
  (*Test method "update_ast_w_sel_dss"*)
  let upd_ast = update_ast_w_sel_dss ast sel_dss_assoc_l in
  let upd_seq1 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"se1_fi1")),
          us"int",
          TmList([(create_mock_tmconst_int 1 (us"seq1_fi2"))]),
          SeqNone,
          0) in
  let upd_app1 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app1_fi1")),
          lam1,
          upd_seq1) in
  let exp_upd_ast = upd_app1 in
  let comp_upd_ast_res = compare_asts upd_ast exp_upd_ast in
  (*Handle complete test result*)
  let test_res = comp_rels_res && comp_seqs_res && comp_seq_cons_res && comp_rels_assoc_l1_res && comp_rels_assoc_l2_res && comp_vis_seqs_assoc_l_res && comp_rels_assoc_l3_res && comp_mf_matrix1_res && comp_sel_dss_assoc_l_res && comp_upd_ast_res in
  let _ = Printf.printf "Test process steps 1: %s\n" (get_test_res_string test_res) in
  true

(*TEST 2: Test all process steps individually
  Program:
    let i = (seqmethod.length [Int]) (newseq [int] (1,2))
  AST:
    TmApp((lam i:Dyn. Nop), TmApp((Seq.length(), TmSeq(1,2))))*)
let run_process_steps_test2 =
    let seq1 =
      TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq1_fi1")),
            us"int",
            TmList([(create_mock_tmconst_int 1 (us"seq1_fi2"));
                    (create_mock_tmconst_int 2 (us"seq1_fi3"))]),
            SeqNone,
            -1) in
    let seqm1 =
      TmSeqMethod((create_mock_ti (get_mock_tyarrow_tyseq_int_gint) (us"seqm1_fi1")),
                  us"length",
                  SeqFunNone,
                  [],
                  0,
                  -1) in
    let app1 =
      TmApp((create_mock_ti (get_mock_gvoid) (us"app1_fi1")),
            seqm1,
            seq1) in
    let lam1 =
      TmLam((create_mock_ti (get_mock_tyarrow_gint_gvoid) (us"lam1_fi1")),
            us"i",
            TyDyn,
            TmNop) in
    let app2 =
      TmApp((create_mock_ti (get_mock_gvoid) (us"app2_fi1")),
            lam1,
            app1) in
    let ast = app2 in
    (*Test method "find_rels_and_seqs_in_ast"*)
    let (rels,seqs) = find_rels_and_seqs_in_ast ast [] [] in
    let exp_rels = [(seqm1,seq1)] in
    let comp_rels_res = compare_rels rels exp_rels in
    let exp_seqs = [seqm1;seq1] in
    let comp_seqs_res = compare_seqs seqs exp_seqs in
    (*Test method "find_seq_cons_among_seqs"*)
    let seq_cons = find_seq_cons_among_seqs seqs in
    let exp_seq_cons = [seq1] in
    let comp_seq_cons_res = compare_seqs seq_cons exp_seq_cons in
    (*Test method "init_rels_assoc_list"*)
    let rels_assoc_l1 = init_rels_assoc_list seqs in
    let exp_rels_assoc_l1 = [(seqm1,[]);(seq1,[])] in
    let comp_rels_assoc_l1_res = compare_rels_assoc_list rels_assoc_l1 exp_rels_assoc_l1 in
    (*Test method "transl_rels_to_rels_assoc_list"*)
    let rels_assoc_l2 = transl_rels_to_rels_assoc_list rels rels_assoc_l1 in
    let exp_rels_assoc_l2 = [(seq1,[seqm1]);(seqm1,[seq1])] in
    let comp_rels_assoc_l2_res = compare_rels_assoc_list rels_assoc_l2 exp_rels_assoc_l2 in
    (*Test method "init_visited_seqs_assoc_list"*)
    let vis_seqs_assoc_l = init_visited_seqs_assoc_list rels_assoc_l2 in
    let exp_vis_seqs_assoc_l = [(seq1,false);(seqm1,false)] in
    let comp_vis_seqs_assoc_l_res = compare_rels vis_seqs_assoc_l exp_vis_seqs_assoc_l in
    (*Test method "reduce_rels"*)
    let rels_assoc_l3 = reduce_rels rels_assoc_l2 (init_visited_seqs_assoc_list rels_assoc_l2) in
    let exp_rels_assoc_l3 = [(seq1,[seqm1])] in
    let comp_rels_assoc_l3_res = compare_rels_assoc_list rels_assoc_l3 exp_rels_assoc_l3 in
    (*Test method "create_mf_matrix"*)
    let mf_matrix1 = create_mf_matrix rels_assoc_l3 in
    let exp_mf_row1 = init_mf_row in
    let upd_exp_mf_row11 = List.remove_assoc ("length") (exp_mf_row1) in
    let upd_exp_mf_row12 = ("length",1)::upd_exp_mf_row11 in
    let comp_mf_matrix1_res = compare_mf_matrix_count mf_matrix1 [upd_exp_mf_row12] in
    (*Run method "Frequencies.translate_mf_assoc_list" - tested in Frequencies*)
    let mf_matrix2 = Frequencies.translate_mf_assoc_list mf_matrix1 in (*TODO: Mock mf_matrix2 instead? Also in above tests?*)
    (*Mock algorithm step - tested in Dssa*)
    let selected_dss = [[0]] in
    (*Test method "connect_seqs_w_sel_dss"*)
    let sel_dss_assoc_l = connect_seqs_w_sel_dss selected_dss rels_assoc_l3 in
    let exp_sel_dss_assoc_l = [(seq1,0);(seqm1,0)] in
    let comp_sel_dss_assoc_l_res = compare_rels sel_dss_assoc_l exp_sel_dss_assoc_l in
    (*Test method "update_ast_w_sel_dss"*)
    let upd_ast = update_ast_w_sel_dss ast sel_dss_assoc_l in
    let upd_seq1 =
      TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq1_fi1")),
            us"int",
            TmList([(create_mock_tmconst_int 1 (us"seq1_fi2"));
                    (create_mock_tmconst_int 2 (us"seq1_fi3"))]),
            SeqNone,
            0) in
    let upd_seqm1 =
      TmSeqMethod((create_mock_ti (get_mock_tyseq_int) (us"seqm1_fi1")),
                  us"length",
                  SeqListFun2(Linkedlist.length),
                  [],
                  0,
                  0) in
    let upd_app1 =
      TmApp((create_mock_ti (get_mock_gvoid) (us"app1_fi1")),
            upd_seqm1,
            upd_seq1) in
    let upd_app2 =
      TmApp((create_mock_ti (get_mock_gvoid) (us"app2_fi1")),
            lam1,
            upd_app1) in
    let exp_upd_ast = upd_app2 in
    let comp_upd_ast_res = compare_asts upd_ast exp_upd_ast in
    (*Handle complete test result*)
    let test_res = comp_rels_res && comp_seqs_res && comp_seq_cons_res && comp_rels_assoc_l1_res && comp_rels_assoc_l2_res && comp_vis_seqs_assoc_l_res && comp_rels_assoc_l3_res && comp_mf_matrix1_res && comp_sel_dss_assoc_l_res && comp_upd_ast_res in
    let _ = Printf.printf "Test process steps 2: %s\n" (get_test_res_string test_res) in
    true

(*TEST 3: Test all process steps individually
  Program:
    let s = (seqmethod.append [Int]) (newseq [int] (1,2)) (newseq [int] (3,4))
  AST:
    TmApp((lam s:Dyn. Nop),
      TmApp((
        TmApp((Seq.append(), TmSeq(1,2))), TmSeq(3,4))))*)
let run_process_steps_test3 =
  let seq1 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq1_fi1")),
          us"int",
          TmList([(create_mock_tmconst_int 3 (us"seq1_fi2"));
                  (create_mock_tmconst_int 4 (us"seq1_fi3"))]),
          SeqNone,
          -1) in
  let seq2 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq2_fi1")),
          us"int",
          TmList([(create_mock_tmconst_int 1 (us"seq2_fi2"));
                  (create_mock_tmconst_int 2 (us"seq2_fi3"))]),
          SeqNone,
          -1) in
  let seqm1 =
    TmSeqMethod((create_mock_ti (get_mock_tyarrow_tyseq_int_tyseq_int_tyseq_int) (us"seqm1_fi1")),
                us"append",
                SeqFunNone,
                [],
                0,
                -1) in
  let app1 =
    TmApp((create_mock_ti (get_mock_tyarrow_tyseq_int_tyseq_int) (us"app1_fi1")),
          seqm1,
          seq2) in
  let app2 =
    TmApp((create_mock_ti (get_mock_tyseq_int) (us"app2_fi1")),
          app1,
          seq1) in
  let lam1 =
    TmLam((create_mock_ti (get_mock_tyarrow_tyseq_int_gvoid) (us"lam1_fi1")),
          us"s",
          TyDyn,
          TmNop) in
  let app3 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app3_fi1")),
          lam1,
          app2) in
  let ast = app3 in
  (*Test method "find_rels_and_seqs_in_ast"*)
  let (rels,seqs) = find_rels_and_seqs_in_ast ast [] [] in
  let exp_rels = [(lam1,seqm1);(seq2,seq1);(seqm1,seq2)] in
  let comp_rels_res = compare_rels rels exp_rels in
  let exp_seqs = [lam1;seqm1;seq2;seq1] in
  let comp_seqs_res = compare_seqs seqs exp_seqs in
  (*Test method "find_seq_cons_among_seqs"*)
  let seq_cons = find_seq_cons_among_seqs seqs in
  let exp_seq_cons = [seq2;seq1] in
  let comp_seq_cons_res = compare_seqs seq_cons exp_seq_cons in
  (*Test method "init_rels_assoc_list"*)
  let rels_assoc_l1 = init_rels_assoc_list seqs in
  let exp_rels_assoc_l1 = [(lam1,[]);(seqm1,[]);(seq2,[]);(seq1,[])] in
  let comp_rels_assoc_l1_res = compare_rels_assoc_list rels_assoc_l1 exp_rels_assoc_l1 in
  (*Test method "transl_rels_to_rels_assoc_list"*)
  let rels_assoc_l2 = transl_rels_to_rels_assoc_list rels rels_assoc_l1 in
  let exp_rels_assoc_l2 = [(seq2,[seqm1;seq1]);(seqm1,[seq2;lam1]);(seq1,[seq2]);(lam1,[seqm1]);] in
  let comp_rels_assoc_l2_res = compare_rels_assoc_list rels_assoc_l2 exp_rels_assoc_l2 in
  (*Test method "init_visited_seqs_assoc_list"*)
  let vis_seqs_assoc_l = init_visited_seqs_assoc_list rels_assoc_l2 in
  let exp_vis_seqs_assoc_l = [(seq2,false);(seqm1,false);(seq1,false);(lam1,false);] in
  let comp_vis_seqs_assoc_l_res = compare_rels vis_seqs_assoc_l exp_vis_seqs_assoc_l in
  (*Test method "reduce_rels"*)
  let rels_assoc_l3 = reduce_rels rels_assoc_l2 (init_visited_seqs_assoc_list rels_assoc_l2) in
  let exp_rels_assoc_l3 = [(seq2,[lam1;seq1;seqm1])] in
  let comp_rels_assoc_l3_res = compare_rels_assoc_list rels_assoc_l3 exp_rels_assoc_l3 in
  (*Test method "create_mf_matrix"*)
  let mf_matrix1 = create_mf_matrix rels_assoc_l3 in
  let exp_mf_row1 = init_mf_row in
  let upd_exp_mf_row11 = List.remove_assoc ("append") (exp_mf_row1) in
  let upd_exp_mf_row12 = ("append",1)::upd_exp_mf_row11 in
  let comp_mf_matrix1_res = compare_mf_matrix_count mf_matrix1 [upd_exp_mf_row12] in
  (*Run method "Frequencies.translate_mf_assoc_list" - tested in Frequencies*)
  let mf_matrix2 = Frequencies.translate_mf_assoc_list mf_matrix1 in (*TODO: Mock mf_matrix2 instead? Also in above tests?*)
  (*Mock algorithm step - tested in Dssa*)
  let selected_dss = [[0]] in
  (*Test method "connect_seqs_w_sel_dss"*)
  let sel_dss_assoc_l = connect_seqs_w_sel_dss selected_dss rels_assoc_l3 in
  let exp_sel_dss_assoc_l = [(seq2,0);(lam1,0);(seq1,0);(seqm1,0)] in
  let comp_sel_dss_assoc_l_res = compare_rels sel_dss_assoc_l exp_sel_dss_assoc_l in
  (*Test method "update_ast_w_sel_dss"*)
  let upd_ast = update_ast_w_sel_dss ast sel_dss_assoc_l in
  let upd_seq1 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq1_fi1")),
          us"int",
          TmList([(create_mock_tmconst_int 3 (us"seq1_fi2"));
                  (create_mock_tmconst_int 4 (us"seq1_fi3"))]),
          SeqNone, (*TODO: Is this set? Check in other tests as well.*)
          0) in
  let upd_seq2 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq2_fi1")),
          us"int",
          TmList([(create_mock_tmconst_int 1 (us"seq2_fi2"));
                  (create_mock_tmconst_int 2 (us"seq2_fi3"))]),
          SeqNone,
          0) in
  let upd_seqm1 =
    TmSeqMethod((create_mock_ti (get_mock_tyarrow_tyseq_int_tyseq_int_tyseq_int) (us"seqm1_fi1")),
                us"append",
                (SeqListFun1(Linkedlist.append)),
                [],
                0,
                0) in
  let upd_app1 =
    TmApp((create_mock_ti (get_mock_tyarrow_tyseq_int_tyseq_int) (us"app1_fi1")),
          upd_seqm1,
          upd_seq2) in
  let upd_app2 =
    TmApp((create_mock_ti (get_mock_tyseq_int) (us"app2_fi1")),
          upd_app1,
          upd_seq1) in
  let upd_app3 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app3_fi1")),
          lam1,
          upd_app2) in
  let exp_upd_ast = upd_app3 in
  let comp_upd_ast_res = compare_asts upd_ast exp_upd_ast in
  (*Handle complete test result*)
  let test_res = comp_rels_res && comp_seqs_res && comp_seq_cons_res && comp_rels_assoc_l1_res && comp_rels_assoc_l2_res && comp_vis_seqs_assoc_l_res && comp_rels_assoc_l3_res && comp_mf_matrix1_res && comp_sel_dss_assoc_l_res && comp_upd_ast_res in
  let _ = Printf.printf "Test process steps 3: %s\n" (get_test_res_string test_res) in
        true
