open Ast
open Linkedlist
open Pprint
open Seqprocessing
open Ustring.Op

(*--- Helper methods ---*)
let get_mock_tyseq_int =
  TySeq(TyGround(NoInfo,GInt))

let get_mock_gvoid =
  TyGround(NoInfo,GVoid)

let get_mock_gint =
  TyGround(NoInfo,GInt)

let get_mock_gbool =
  TyGround(NoInfo,GBool)

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

let get_mock_tyarrow_gint_gint =
  TyArrow(NoInfo,
          get_mock_gint,
          get_mock_gint)

let get_mock_tyarrow_gint_gbool =
  TyArrow(NoInfo,
          get_mock_gint,
          get_mock_gbool)

let get_mock_tyarrow_gint_gint_gint =
  TyArrow(NoInfo,
          get_mock_gint,
          TyArrow(NoInfo,
                  get_mock_gint,
                  get_mock_gint))

let get_mock_tyarrow_gint_gint_gbool =
  TyArrow(NoInfo,
          get_mock_gint,
          TyArrow(NoInfo,
                  get_mock_gint,
                  get_mock_gbool))

let get_mock_tyarrow_tyarrow_gint_gint_gint_gint =
  TyArrow(NoInfo,
          TyArrow(NoInfo,
                  get_mock_gint,
                  get_mock_gint),
          TyArrow(NoInfo,
                  get_mock_gint,
                  get_mock_gint))

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
  match t1, t2 with
  | TmChar(_,n1),TmChar(_,n2) -> n1 = n2
  | TmConst(_,c1),TmConst(_,c2) -> c1 = c2
  | TmNop, TmNop -> true
  | TmVar(_,id1,_,_), TmVar(_,id2,_,_) -> id1 = id2
  | TmLam(_,var1,ty1,tm1), TmLam(_,var2,ty2,tm2) ->
    ((Ustring.to_utf8 var1) = (Ustring.to_utf8 var2)) && (Typesys.tyequal ty1 ty2) && (compare_terms tm1 tm2)
  | TmClos(_,var1,ty1,tm1,_,_), TmClos(_,var2,ty2,tm2,_,_) ->
    (var1 == var2) && (Typesys.tyequal ty1 ty2) && (compare_terms tm1 tm2)
  | TmApp(_,tm11,tm12), TmApp(_,tm21,tm22) ->
    (compare_terms tm11 tm21) && (compare_terms tm12 tm22)
  | TmIfexp(_,tm11,tm12,tm13), TmIfexp(_,tm21,tm22,tm23) ->
    (compare_terms tm11 tm21) && (compare_terms tm12 tm22) && (compare_terms tm13 tm23)
  | TmFix _, TmFix _ -> true
  | TmSeq(_,_,tm_l1,_,ds_choice1), TmSeq(_,_,tm_l2,_,ds_choice2) ->
    (compare_term_lists (get_list_from_tmlist tm_l1) (get_list_from_tmlist tm_l2)) && (ds_choice1 == ds_choice2) (*TODO: Check tmseq as well*)
  | TmSeqMethod(_,fun_name1,_,_,_,ds_choice1,in_fix1), TmSeqMethod(_,fun_name2,_,_,_,ds_choice2,in_fix2) ->
    ((Ustring.to_utf8 fun_name1) = (Ustring.to_utf8 fun_name2)) && (ds_choice1 == ds_choice2) && (in_fix1 == in_fix2) (*TODO: Check actual_fun as well?*)
  | _ ->
    false

let rec compare_tm_const_pair_list rels1 rels2 =
  match rels1, rels2 with
  | [], [] -> true
  | [], _ | _, [] -> false
  | (hd11,hd12)::tl1, (hd21,hd22)::tl2 ->
    if (compare_terms hd11 hd21) && (hd12 == hd22) then
      compare_tm_const_pair_list tl1 tl2
    else
      false

let rec compare_rels rels1 rels2 =
  match rels1, rels2 with
  | [], [] -> true
  | [], _ | _, [] -> false
  | (hd11,hd12)::tl1, (hd21,hd22)::tl2 ->
    if (compare_terms hd11 hd21) && (compare_terms hd12 hd22) then
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
  let (rels,seqs) = find_rels_and_seqs_in_ast ast [] [] false in
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
  let comp_vis_seqs_assoc_l_res = compare_tm_const_pair_list vis_seqs_assoc_l exp_vis_seqs_assoc_l in
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
  let comp_sel_dss_assoc_l_res = compare_tm_const_pair_list sel_dss_assoc_l exp_sel_dss_assoc_l in
  (*Test method "update_ast_w_sel_dss"*)
  let upd_ast = update_ast_w_sel_dss ast sel_dss_assoc_l false in
  let upd_seq1 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"se1_fi1")),
          us"int",
          TmList([]),
          SeqList(Linkedlist.from_list [(create_mock_tmconst_int 1 (us"seq1_fi2"))]),
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
                  -1,
                 false) in
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
    let (rels,seqs) = find_rels_and_seqs_in_ast ast [] [] false in
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
    let comp_vis_seqs_assoc_l_res = compare_tm_const_pair_list vis_seqs_assoc_l exp_vis_seqs_assoc_l in
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
    let comp_sel_dss_assoc_l_res = compare_tm_const_pair_list sel_dss_assoc_l exp_sel_dss_assoc_l in
    (*Test method "update_ast_w_sel_dss"*)
    let upd_ast = update_ast_w_sel_dss ast sel_dss_assoc_l false in
    let upd_seq1 =
      TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq1_fi1")),
            us"int",
            TmList([]),
            SeqList(Linkedlist.from_list [(create_mock_tmconst_int 1 (us"seq1_fi2")); (create_mock_tmconst_int 2 (us"seq1_fi3"))]),
            0) in
    let upd_seqm1 =
      TmSeqMethod((create_mock_ti (get_mock_tyseq_int) (us"seqm1_fi1")),
                  us"length",
                  SeqListFun2(Linkedlist.length),
                  [],
                  0,
                  0,
                 false) in
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
                -1,
                false) in
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
  let (rels,seqs) = find_rels_and_seqs_in_ast ast [] [] false in
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
  let comp_vis_seqs_assoc_l_res = compare_tm_const_pair_list vis_seqs_assoc_l exp_vis_seqs_assoc_l in
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
  let comp_sel_dss_assoc_l_res = compare_tm_const_pair_list sel_dss_assoc_l exp_sel_dss_assoc_l in
  (*Test method "update_ast_w_sel_dss"*)
  let upd_ast = update_ast_w_sel_dss ast sel_dss_assoc_l false in
  let upd_seq1 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq1_fi1")),
          us"int",
          TmList([]),
          SeqList(Linkedlist.from_list [(create_mock_tmconst_int 3 (us"seq1_fi2")); (create_mock_tmconst_int 4 (us"seq1_fi3"))]), (*TODO: Is this set? Check in other tests as well.*)
          0) in
  let upd_seq2 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq2_fi1")),
          us"int",
          TmList([]),
          SeqList(Linkedlist.from_list [(create_mock_tmconst_int 1 (us"seq2_fi2")); (create_mock_tmconst_int 2 (us"seq2_fi3"))]),
          0) in
  let upd_seqm1 =
    TmSeqMethod((create_mock_ti (get_mock_tyarrow_tyseq_int_tyseq_int_tyseq_int) (us"seqm1_fi1")),
                us"append",
                (SeqListFun1(Linkedlist.append)),
                [],
                0,
                0,
                false) in
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

(*TEST 3: Test all process steps individually
  Program:
    let s = (seqmethod.append [Int]) (newseq [int] (1,2)) (newseq [int] (3,4))
  AST:
    TmApp((lam s:Dyn. Nop),
      TmApp((
        TmApp((Seq.append(), TmSeq(1,2))), TmSeq(3,4))))*)

          (*
          TmApp(
          (lam s1:Dyn.
                    TmApp(
                        (lam s2:Dyn.
                                  TmApp((lam l:Dyn. Nop),
                                        TmApp((Seq.length(NO Fun){-1}, TmVar(s1'1))))),
                        TmSeq(3,4)(){-1})),
          TmSeq(1,2)(){-1})*)
let run_process_steps_test4 =
  (*TmSeq(1,2)(){-1} with type TySeq[Int]*)
  let seq1 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq1_fi1")),
          us"int",
          TmList([(create_mock_tmconst_int 1 (us"seq1_fi2"));
                  (create_mock_tmconst_int 2 (us"seq1_fi3"));]),
          SeqNone,
          -1) in
  (*TmSeq(3,4)(){-1} with type TySeq[Int]*)
  let seq2 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq2_fi1")),
          us"int",
          TmList([(create_mock_tmconst_int 3 (us"seq2_fi2"));
                  (create_mock_tmconst_int 4 (us"seq2_fi3"));]),
          SeqNone,
          -1) in
  (*TmVar(s1'1) with type TySeq[Int]*)
  let var1 =
    TmVar((create_mock_ti (get_mock_tyseq_int) (us"var1_fi1")),
          us"s1",
          1,
          false) in
  (*Seq.length(NO Fun){-1} with type (TySeq[Int]->Int)*)
  let seqm1 =
    TmSeqMethod((create_mock_ti (get_mock_tyarrow_tyseq_int_gint) (us"seqm1_fi1")),
                us"length",
                SeqFunNone,
                [],
                0,
                -1,
                false) in
  (*TmApp(seqm1; var1) with type Int*)
  let app1 =
    TmApp((create_mock_ti (get_mock_gint) (us"app1_fi")),
          seqm1,
          var1) in
  (*lam l:Dyn. Nop with type (Int->Void)*)
  let lam1 =
    TmLam((create_mock_ti (get_mock_tyarrow_gint_gvoid) (us"lam1_fi1")),
          us"l",
          TyDyn,
          TmNop) in
  (*TmApp((lam1); TmApp((seqm1; var1))) with type Void*)
  let app2 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app2_fi1")),
          lam1,
          app1) in
  (*lam s2:Dyn. app2 with type (TySeq[Int]->Void)*)
  let lam2 =
    TmLam((create_mock_ti (get_mock_tyarrow_tyseq_int_gvoid) (us"lam2_fi1")),
          us"s2",
          TyDyn,
          app2) in
  (*TmApp((lam2); seq2) with type Void*)
  let app3 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app3_fi1")),
          lam2,
          seq2) in
  (*lam s1:Dyn. app3 with type (TySeq[Int]->Void)*)
  let lam3 =
    TmLam((create_mock_ti (get_mock_tyarrow_tyseq_int_gvoid) (us"lam3_fi1")),
          us"s1",
          TyDyn,
          app3) in
  (*TmApp((lam3); seq1) with type Void*)
  let app4 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app4_fi1")),
          lam3,
          seq1) in
  let ast = app4 in
  (*Test method "find_rels_and_seqs_in_ast"*)
  let (rls,seqs) = find_rels_and_seqs_in_ast ast [] [] false in
  let rels = find_lam_var_rels seqs rls seqs in (*TODO:Add this to above testcases*)
  let exp_rels = [(lam3,var1);(lam3,seq1);(lam2,seq2);(seqm1,var1)] in
  let comp_rels_res = compare_rels rels exp_rels in
  let exp_seqs = [seqm1;var1;lam2;seq2;lam3;seq1] in
  let comp_seqs_res = compare_seqs seqs exp_seqs in
  (*Test method "find_seq_cons_among_seqs"*)
  let seq_cons = find_seq_cons_among_seqs seqs in
  let exp_seq_cons = [seq2;seq1] in
  let comp_seq_cons_res = compare_seqs seq_cons exp_seq_cons in
  (*Test method "init_rels_assoc_list"*)
  let rels_assoc_l1 = init_rels_assoc_list seqs in
  let exp_rels_assoc_l1 = [(seqm1,[]);(var1,[]);(lam2,[]);(seq2,[]);(lam3,[]);(seq1,[])] in
  let comp_rels_assoc_l1_res = compare_rels_assoc_list rels_assoc_l1 exp_rels_assoc_l1 in
  (*Test method "transl_rels_to_rels_assoc_list"*)
  let rels_assoc_l2 = transl_rels_to_rels_assoc_list rels rels_assoc_l1 in
  let exp_rels_assoc_l2 = [(var1,[seqm1;lam3]);(seqm1,[var1]);(seq2,[lam2]);(lam2,[seq2]);(seq1,[lam3]);(lam3,[seq1;var1])] in
  let comp_rels_assoc_l2_res = compare_rels_assoc_list rels_assoc_l2 exp_rels_assoc_l2 in
  (*Test method "init_visited_seqs_assoc_list"*)
  let vis_seqs_assoc_l = init_visited_seqs_assoc_list rels_assoc_l2 in
  let exp_vis_seqs_assoc_l = [(var1,false);(seqm1,false);(seq2,false);(lam2,false);(seq1,false);(lam3,false)] in
  let comp_vis_seqs_assoc_l_res = compare_tm_const_pair_list vis_seqs_assoc_l exp_vis_seqs_assoc_l in
  (*Test method "reduce_rels"*)
  let rels_assoc_l3 = reduce_rels rels_assoc_l2 (init_visited_seqs_assoc_list rels_assoc_l2) in
  let exp_rels_assoc_l3 = [(var1,[seq1;lam3;seqm1]);(seq2,[lam2])] in
  let comp_rels_assoc_l3_res = compare_rels_assoc_list rels_assoc_l3 exp_rels_assoc_l3 in
  (*Test method "create_mf_matrix"*)
  let mf_matrix1 = create_mf_matrix rels_assoc_l3 in
  let exp_mf_row1 = init_mf_row in
  let upd_exp_mf_row11 = List.remove_assoc ("length") (exp_mf_row1) in
  let upd_exp_mf_row12 = ("length",1)::upd_exp_mf_row11 in
  let exp_mf_row2 = init_mf_row in
  let comp_mf_matrix1_res = compare_mf_matrix_count mf_matrix1 [upd_exp_mf_row12;exp_mf_row2] in
  (*Run method "Frequencies.translate_mf_assoc_list" - tested in Frequencies*)
  let mf_matrix2 = Frequencies.translate_mf_assoc_list mf_matrix1 in (*TODO: Mock mf_matrix2 instead? Also in above tests?*)
  (*Mock algorithm step - tested in Dssa*)
  let selected_dss = [[0];[1]] in
  (*Test method "connect_seqs_w_sel_dss"*)
  let sel_dss_assoc_l = connect_seqs_w_sel_dss selected_dss rels_assoc_l3 in
  let exp_sel_dss_assoc_l = [(var1,0);(seq1,0);(lam3,0);(seqm1,0);(seq2,1);(lam2,1)] in
  let comp_sel_dss_assoc_l_res = compare_tm_const_pair_list sel_dss_assoc_l exp_sel_dss_assoc_l in
  (*Test method "update_ast_w_sel_dss"*)
  let upd_ast = update_ast_w_sel_dss ast sel_dss_assoc_l false in
  let upd_seq1 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq1_fi1")),
          us"int",
          TmList([]),
          SeqList(Linkedlist.from_list [(create_mock_tmconst_int 1 (us"seq1_fi2")); (create_mock_tmconst_int 2 (us"seq1_fi3"));]),
          0) in
  let upd_seq2 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq2_fi1")),
          us"int",
          TmList([]),
          SeqList(Linkedlist.from_list [(create_mock_tmconst_int 3 (us"seq2_fi2")); (create_mock_tmconst_int 4 (us"seq2_fi3"));]),
          1) in
  let upd_seqm1 =
    TmSeqMethod((create_mock_ti (get_mock_tyarrow_tyseq_int_gint) (us"seqm1_fi1")),
                us"length",
                SeqListFun2(Linkedlist.length),
                [],
                0,
                0,
                false) in
  let upd_app1 =
    TmApp((create_mock_ti (get_mock_gint) (us"app1_fi")),
          upd_seqm1,
          var1) in
  let upd_app2 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app2_fi1")),
          lam1,
          upd_app1) in
  let upd_lam2 =
    TmLam((create_mock_ti (get_mock_tyarrow_tyseq_int_gvoid) (us"lam2_fi1")),
          us"s2",
          TyDyn,
          upd_app2) in
  let upd_app3 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app3_fi1")),
          upd_lam2,
          upd_seq2) in
  let upd_lam3 =
    TmLam((create_mock_ti (get_mock_tyarrow_tyseq_int_gvoid) (us"lam3_fi1")),
          us"s1",
          TyDyn,
          upd_app3) in
  let upd_app4 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app4_fi1")),
          upd_lam3,
          upd_seq1) in
  let exp_upd_ast = upd_app4 in
  let comp_upd_ast_res = compare_asts upd_ast exp_upd_ast in
  (*Handle complete test result*)
  let test_res = comp_seqs_res && comp_rels_res && comp_seq_cons_res && comp_rels_assoc_l1_res && comp_rels_assoc_l2_res && comp_vis_seqs_assoc_l_res && comp_rels_assoc_l3_res && comp_mf_matrix1_res && comp_sel_dss_assoc_l_res && comp_upd_ast_res in
  let _ = Printf.printf "Test process steps 4: %s\n" (get_test_res_string test_res) in
  true

let run_process_steps_test5 =
  (*TmSeq(1)(){-1} with type TySeq[Int]*)
  let seq1 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq1_fi1")),
          us"int",
          TmList([(create_mock_tmconst_int 1 (us"seq1_fi2"))]),
          SeqNone,
          -1) in
  (*TmSeq(2)(){-1} with type TySeq[Int]*)
  let seq2 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq2_fi1")),
          us"int",
          TmList([(create_mock_tmconst_int 2 (us"seq2_fi2"))]),
          SeqNone,
          -1) in
  (*TmVar(s1'1) with type TySeq[Int]*)
  let var1 =
    TmVar((create_mock_ti (get_mock_tyseq_int) (us"var1_fi1")),
          us"s1",
          1,
          false) in
  (*TmVar(s3'0) with type TySeq[Int]*)
  let var2 =
    TmVar((create_mock_ti (get_mock_tyseq_int) (us"var2_fi1")),
          us"s3",
          0,
          false) in
  (*TmVar(s2'1) with type TySeq[Int]*)
  let var3 =
    TmVar((create_mock_ti (get_mock_tyseq_int) (us"var3_fi1")),
          us"s2",
          1,
          false) in
  (*Seq.append(NO Fun){-1} with type (TySeq[Int]->TySeq[Int]->TySeq[Int])*)
  let seqm1 =
    TmSeqMethod((create_mock_ti (get_mock_tyarrow_tyseq_int_tyseq_int_tyseq_int) (us"seqm1_fi1")),
                us"append",
                SeqFunNone,
                [],
                0,
                -1,
                false) in
  (*TmApp(seqm1; var3) with type (TySeq[Int]->TySeq[Int])*)
  let app1 =
    TmApp((create_mock_ti (get_mock_tyarrow_tyseq_int_tyseq_int) (us"app1_fi1")),
          seqm1,
          var3) in
  (*TmApp(app1; var2) with type TySeq[Int]*)
  let app2 =
    TmApp((create_mock_ti (get_mock_tyseq_int) (us"app2_fi1")),
          app1,
          var2) in
  (*lam s4:Dyn. Nop with type (TySeq[Int]->Void)*)
  let lam1 =
    TmLam((create_mock_ti (get_mock_tyarrow_tyseq_int_gvoid) (us"lam1_fi1")),
          us"s4",
          TyDyn,
          TmNop) in
  (*TmApp((lam1); app2) with type Void*)
  let app3 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app3_fi1")),
          lam1,
          app2) in
  (*lam s3:Dyn. app3 with type (TySeq[Int]->Void)*)
  let lam2 =
    TmLam((create_mock_ti (get_mock_tyarrow_tyseq_int_gvoid) (us"lam2_fi1")),
          us"s3",
          TyDyn,
          app3) in
  (*TmApp((lam2); var1) with type Void*)
  let app4 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app4_fi1")),
          lam2,
          var1) in
  (*lam s2:Dyn. app4 with type (TySeq[Int]->Void)*)
  let lam3 =
    TmLam((create_mock_ti (get_mock_tyarrow_tyseq_int_gvoid) (us"lam3_fi1")),
          us"s2",
          TyDyn,
          app4) in
  (*TmApp((lam3); seq2) with type Void*)
  let app5 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app5_fi1")),
          lam3,
          seq2) in
  (*lam s1:Dyn. app5 with type (TySeq[Int]->Void)*)
  let lam4 =
    TmLam((create_mock_ti (get_mock_tyarrow_tyseq_int_gvoid) (us"lam4_fi1")),
          us"s1",
          TyDyn,
          app5) in
  (*TmApp((lam4); seq1) with type Void*)
  let app6 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app6_fi1")),
          lam4,
          seq1) in
  let ast = app6 in
  (*Test method "find_rels_and_seqs_in_ast"*)
  let (rls,seqs) = find_rels_and_seqs_in_ast ast [] [] false in
  let rels = find_lam_var_rels seqs rls seqs in (*TODO:Add this to above testcases*)
  let exp_rels = [(lam4,var1);(lam3,var3);(lam2,var2);(lam4,seq1);(lam3,seq2);(lam2,var1);(lam1,seqm1);(var3,var2);(seqm1,var3)] in
  let comp_rels_res = compare_rels rels exp_rels in
  let exp_seqs = [lam1;seqm1;var3;var2;lam2;var1;lam3;seq2;lam4;seq1] in
  let comp_seqs_res = compare_seqs seqs exp_seqs in
  (*Test method "find_seq_cons_among_seqs"*)
  let seq_cons = find_seq_cons_among_seqs seqs in
  let exp_seq_cons = [seq2;seq1] in
  let comp_seq_cons_res = compare_seqs seq_cons exp_seq_cons in
  (*Test method "init_rels_assoc_list"*)
  let rels_assoc_l1 = init_rels_assoc_list seqs in
  let exp_rels_assoc_l1 = [(lam1,[]);(seqm1,[]);(var3,[]);(var2,[]);(lam2,[]);(var1,[]);(lam3,[]);(seq2,[]);(lam4,[]);(seq1,[])] in
  let comp_rels_assoc_l1_res = compare_rels_assoc_list rels_assoc_l1 exp_rels_assoc_l1 in
  (*Test method "transl_rels_to_rels_assoc_list"*)
  let rels_assoc_l2 = transl_rels_to_rels_assoc_list rels rels_assoc_l1 in
  let exp_rels_assoc_l2 = [(var3,[seqm1;var2;lam3]);(seqm1,[var3;lam1]);(var2,[var3;lam2]);(lam1,[seqm1]);(var1,[lam2;lam4]);(lam2,[var1;var2]);(seq2,[lam3]);(lam3,[seq2;var3]);(seq1,[lam4]);(lam4,[seq1;var1])] in
  let comp_rels_assoc_l2_res = compare_rels_assoc_list rels_assoc_l2 exp_rels_assoc_l2 in
  (*Test method "init_visited_seqs_assoc_list"*)
  let vis_seqs_assoc_l = init_visited_seqs_assoc_list rels_assoc_l2 in
  let exp_vis_seqs_assoc_l = [(var3,false);(seqm1,false);(var2,false);(lam1,false);(var1,false);(lam2,false);(seq2,false);(lam3,false);(seq1,false);(lam4,false)] in
  let comp_vis_seqs_assoc_l_res = compare_tm_const_pair_list vis_seqs_assoc_l exp_vis_seqs_assoc_l in
  (*Test method "reduce_rels"*)
  let rels_assoc_l3 = reduce_rels rels_assoc_l2 (init_visited_seqs_assoc_list rels_assoc_l2) in
  let exp_rels_assoc_l3 = [(var3,[seq1;lam4;var1;lam1;lam2;seq2;lam3;var2;seqm1])] in
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
  let exp_sel_dss_assoc_l = [(var3,0);(seq1,0);(lam4,0);(var1,0);(lam1,0);(lam2,0);(seq2,0);(lam3,0);(var2,0);(seqm1,0)] in
  let comp_sel_dss_assoc_l_res = compare_tm_const_pair_list sel_dss_assoc_l exp_sel_dss_assoc_l in
  (*Test method "update_ast_w_sel_dss"*)
  let upd_ast = update_ast_w_sel_dss ast sel_dss_assoc_l false in
  let upd_seq1 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq1_fi1")),
          us"int",
          TmList([]),
          SeqList(Linkedlist.from_list [(create_mock_tmconst_int 1 (us"seq1_fi2"))]),
          0) in
  let upd_seq2 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq2_fi1")),
          us"int",
          TmList([]),
          SeqList(Linkedlist.from_list [(create_mock_tmconst_int 2 (us"seq2_fi2"))]),
          0) in
  let upd_seqm1 =
    TmSeqMethod((create_mock_ti (get_mock_tyarrow_tyseq_int_tyseq_int_tyseq_int) (us"seqm1_fi1")),
                us"append",
                SeqListFun1(Linkedlist.append),
                [],
                0,
                0,
                false) in
  let upd_app1 =
    TmApp((create_mock_ti (get_mock_tyarrow_tyseq_int_tyseq_int) (us"app1_fi1")),
          upd_seqm1,
          var3) in
  let upd_app2 =
    TmApp((create_mock_ti (get_mock_tyseq_int) (us"app2_fi1")),
          upd_app1,
          var2) in
  let upd_app3 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app3_fi1")),
          lam1,
          upd_app2) in
  let upd_lam2 =
    TmLam((create_mock_ti (get_mock_tyarrow_tyseq_int_gvoid) (us"lam2_fi1")),
          us"s3",
          TyDyn,
          upd_app3) in
  let upd_app4 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app4_fi1")),
          upd_lam2,
          var1) in
  let upd_lam3 =
    TmLam((create_mock_ti (get_mock_tyarrow_tyseq_int_gvoid) (us"lam3_fi1")),
          us"s2",
          TyDyn,
          upd_app4) in
  let upd_app5 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app5_fi1")),
          upd_lam3,
          upd_seq2) in
  let upd_lam4 =
    TmLam((create_mock_ti (get_mock_tyarrow_tyseq_int_gvoid) (us"lam4_fi1")),
          us"s1",
          TyDyn,
          upd_app5) in
  let upd_app6 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app6_fi1")),
          upd_lam4,
          upd_seq1) in
  let exp_upd_ast = upd_app6 in
  let comp_upd_ast_res = compare_asts upd_ast exp_upd_ast in
  (*Handle complete test result*)
  let test_res =  comp_rels_res && comp_seqs_res && comp_seq_cons_res && comp_rels_assoc_l1_res && comp_rels_assoc_l2_res && comp_vis_seqs_assoc_l_res && comp_rels_assoc_l3_res && comp_mf_matrix1_res && comp_sel_dss_assoc_l_res && comp_upd_ast_res in
let _ = Printf.printf "Test process steps 5: %s\n" (get_test_res_string test_res) in
true

let run_process_steps_test6 =
  (*lam f2:Dyn. Nop with type (Int->Void)*)
  let lam_f2 =
    TmLam((create_mock_ti (get_mock_tyarrow_gint_gvoid) (us"lam_f2_fi1")),
          us"f2",
          TyDyn,
          TmNop) in
  (*TmApp((lam_f2), 2) with type Void*)
  let app1 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app1_fi1")),
          lam_f2,
          (create_mock_tmconst_int 2 (us"app1_fi2"))) in
  let ast = app1 in
  (*Test method "find_rels_and_seqs_in_ast"*)
  let (rls,seqs) = find_rels_and_seqs_in_ast ast [] [] false in
  let rels = find_lam_var_rels seqs rls seqs in (*TODO:Add this to above testcases*)
  let exp_rels = [] in
  let comp_rels_res = compare_rels rels exp_rels in
  let exp_seqs = [] in
  let comp_seqs_res = compare_seqs seqs exp_seqs in
  (*Test method "find_seq_cons_among_seqs"*)
  let seq_cons = find_seq_cons_among_seqs seqs in
  let exp_seq_cons = [] in
  let comp_seq_cons_res = compare_seqs seq_cons exp_seq_cons in
  (*Test method "init_rels_assoc_list"*)
  let rels_assoc_l1 = init_rels_assoc_list seqs in
  let exp_rels_assoc_l1 = [] in
  let comp_rels_assoc_l1_res = compare_rels_assoc_list rels_assoc_l1 exp_rels_assoc_l1 in
  (*Test method "transl_rels_to_rels_assoc_list"*)
  let rels_assoc_l2 = transl_rels_to_rels_assoc_list rels rels_assoc_l1 in
  let exp_rels_assoc_l2 = [] in
  let comp_rels_assoc_l2_res = compare_rels_assoc_list rels_assoc_l2 exp_rels_assoc_l2 in
  (*Test method "init_visited_seqs_assoc_list"*)
  let vis_seqs_assoc_l = init_visited_seqs_assoc_list rels_assoc_l2 in
  let exp_vis_seqs_assoc_l = [] in
  let comp_vis_seqs_assoc_l_res = compare_tm_const_pair_list vis_seqs_assoc_l exp_vis_seqs_assoc_l in
  (*Test method "reduce_rels"*)
  let rels_assoc_l3 = reduce_rels rels_assoc_l2 (init_visited_seqs_assoc_list rels_assoc_l2) in
  let exp_rels_assoc_l3 = [] in
  let comp_rels_assoc_l3_res = compare_rels_assoc_list rels_assoc_l3 exp_rels_assoc_l3 in
  (*Test method "create_mf_matrix"*)
  let mf_matrix1 = create_mf_matrix rels_assoc_l3 in
  let comp_mf_matrix1_res = compare_mf_matrix_count mf_matrix1 [] in
  (*Run method "Frequencies.translate_mf_assoc_list" - tested in Frequencies*)
  let mf_matrix2 = Frequencies.translate_mf_assoc_list mf_matrix1 in (*TODO: Mock mf_matrix2 instead? Also in above tests?*)
  (*Mock algorithm step - tested in Dssa*)
  let selected_dss = [] in
  (*Test method "connect_seqs_w_sel_dss"*)
  let sel_dss_assoc_l = connect_seqs_w_sel_dss selected_dss rels_assoc_l3 in
  let exp_sel_dss_assoc_l = [] in
  let comp_sel_dss_assoc_l_res = compare_rels sel_dss_assoc_l exp_sel_dss_assoc_l in
  (*Test method "update_ast_w_sel_dss"*)
  let upd_ast = update_ast_w_sel_dss ast sel_dss_assoc_l false in
  let exp_upd_ast = ast in
  let comp_upd_ast_res = compare_asts upd_ast exp_upd_ast in
  (*Handle complete test result*)
  let test_res = comp_rels_res && comp_seqs_res && comp_seq_cons_res && comp_rels_assoc_l1_res && comp_rels_assoc_l2_res && comp_vis_seqs_assoc_l_res && comp_rels_assoc_l3_res && comp_mf_matrix1_res && comp_sel_dss_assoc_l_res && comp_upd_ast_res in
  let _ = Printf.printf "Test process steps 6: %s\n" (get_test_res_string test_res) in
  true

let run_process_steps_test7 =
  (*TmVar(x'0) with type Int*)
  let var_x =
    TmVar((create_mock_ti (get_mock_gint) (us"varx_fi1")),
          us"x",
          0,
          false) in
  (*TmVar(addi'5) with type (Int->Int->Int)*)
  let var_addi =
    TmVar((create_mock_ti (get_mock_tyarrow_gint_gint_gint) (us"var_addi_fi1")),
          us"addi",
          5,
          false) in
  (*TmApp(var_addi, var_x) with type (Int->Int)*)
  let app1 =
    TmApp((create_mock_ti (get_mock_tyarrow_gint_gint) (us"app1_fi1")),
          var_addi,
          var_x) in
  (*TmApp(app1, 1) with type Int*)
  let app2 =
    TmApp((create_mock_ti (get_mock_gint) (us"app2_fi1")),
          app1,
          (create_mock_tmconst_int 1 (us"app2_fi2"))) in
  (*TmVar(fix_test'1) with type (Int->Int)*)
  let var_fix_test =
    TmVar((create_mock_ti (get_mock_tyarrow_gint_gint) (us"var_fix_test_fi1")),
          us"fix_test",
          1,
          false) in
  (*TmApp(var_fix_test, app2) with type Int*)
  let app3 =
    TmApp((create_mock_ti (get_mock_gint) (us"app3_fi1")),
          var_fix_test,
          app2) in
  (*TmSeq(var_x)(){-1} with type TySeq[Int]*)
  let seq1 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq1_fi1")),
          us"int",
          TmList([var_x]),
          SeqNone,
          -1) in
  (*Seq.length(NO Fun){-1}in_fix:false with type (TySeq[Int]->Int)*)
  let seqm_length =
    TmSeqMethod((create_mock_ti (get_mock_tyarrow_tyseq_int_gint) (us"seqm_length_fi1")),
                us"length",
                SeqFunNone,
                [],
                0,
                -1,
                false) in
  (*TmApp(seqm_length, seq1) with type Int*)
  let app4 =
    TmApp((create_mock_ti (get_mock_gint) (us"app4_fi1")),
          seqm_length,
          seq1) in
  (*lam s:Dyn. TmVar(x'1) with type (Int->Int)*)
  let lam_s =
    TmLam((create_mock_ti (get_mock_tyarrow_gint_gint) (us"lam_s_fi1")),
          us"s",
          TyDyn,
          var_x) in
  (*TmApp((lam_s), app4) with type Int*)
  let app5 =
    TmApp((create_mock_ti (get_mock_gint) (us"app5_fi1")),
          lam_s,
          app4) in
  (*TmVar(leqi'12) with type (Int->Int->Bool)*)
  let var_leqi =
  TmVar((create_mock_ti (get_mock_tyarrow_gint_gint_gbool) (us"var_leqi_fi1")),
        us"leqi",
        12,
        false) in
  (*TmApp(var_leqi, var_x) with type (Int->Bool)*)
  let app6 =
    TmApp((create_mock_ti (get_mock_tyarrow_gint_gbool) (us"app6_fi1")),
          var_leqi,
          var_x) in
  (*TmApp(app6, 3) with type Bool*)
  let app7 =
    TmApp((create_mock_ti (get_mock_gbool) (us"app7_fi1")),
          app6,
          (create_mock_tmconst_int 3 (us"app7_fi2"))) in
  (*if app7 then app5 else app3 with type Int*)
  let if1 =
    TmIfexp((create_mock_ti (get_mock_gint) (us"if1_fi1")),
            app7,
            app5,
            app3) in
  (*lam x:Int. if1 with type (Int->Int)*)
  let lam_x =
    TmLam((create_mock_ti (get_mock_tyarrow_gint_gint) (us"lam_x_fi1")),
          us"x",
          get_mock_gint,
          if1) in
  (*lam fix_test:(Int->Int). lam_x with type ((Int->Int)->Int->Int)*)
  let lam_fix_test =
    TmLam((create_mock_ti (get_mock_tyarrow_tyarrow_gint_gint_gint_gint) (us"lam_fix_test_fi1")),
          us"fix_test",
          get_mock_tyarrow_gint_gint,
          lam_x) in
  (*TmApp(fix, (lam_fix_test)) with type Int*)
  let app8 =
    TmApp((create_mock_ti (get_mock_gint) (us"app8_fi1")),
          TmFix(create_mock_ti (get_mock_gvoid) (us"app8_fi2")),
          lam_fix_test) in
  (*lam fix_test:Dyn. Nop with type (Int->Void)*)
  let lam_fix_test2 =
    TmLam((create_mock_ti (get_mock_tyarrow_gint_gvoid) (us"lam_fix_test2_fix1")),
          us"lam_fix_test",
          TyDyn,
          TmNop) in
  (*TmApp((lam_fix_test_2), app8) with type Void*)
  let app9 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app9_fi1")),
          lam_fix_test2,
          app8) in
  let ast = app9 in
  (*Test method "find_rels_and_seqs_in_ast"*)
  let (rls,seqs) = find_rels_and_seqs_in_ast ast [] [] false in
  let rels = find_lam_var_rels seqs rls seqs in (*TODO:Add this to above testcases*)
  let exp_upd_seqm_length =
    TmSeqMethod((create_mock_ti (get_mock_tyarrow_tyseq_int_gint) (us"seqm_length_fi1")),
                us"length",
                SeqFunNone,
                [],
                0,
                -1,
                true) in
  let exp_rels = [(exp_upd_seqm_length,seq1)] in
  let comp_rels_res = compare_rels rels exp_rels in
  let exp_seqs = [exp_upd_seqm_length;seq1] in
  let comp_seqs_res = compare_seqs seqs exp_seqs in
  (*Test method "find_seq_cons_among_seqs"*)
  let seq_cons = find_seq_cons_among_seqs seqs in
  let exp_seq_cons = [seq1] in
  let comp_seq_cons_res = compare_seqs seq_cons exp_seq_cons in
  (*Test method "init_rels_assoc_list"*)
  let rels_assoc_l1 = init_rels_assoc_list seqs in
  let exp_rels_assoc_l1 = [(exp_upd_seqm_length,[]);(seq1,[])] in
  let comp_rels_assoc_l1_res = compare_rels_assoc_list rels_assoc_l1 exp_rels_assoc_l1 in
  (*Test method "transl_rels_to_rels_assoc_list"*)
  let rels_assoc_l2 = transl_rels_to_rels_assoc_list rels rels_assoc_l1 in
  let exp_rels_assoc_l2 = [(seq1,[exp_upd_seqm_length]);(exp_upd_seqm_length,[seq1]);] in
  let comp_rels_assoc_l2_res = compare_rels_assoc_list rels_assoc_l2 exp_rels_assoc_l2 in
  (*Test method "init_visited_seqs_assoc_list"*)
  let vis_seqs_assoc_l = init_visited_seqs_assoc_list rels_assoc_l2 in
  let exp_vis_seqs_assoc_l = [(seq1,false);(exp_upd_seqm_length,false)] in
  let comp_vis_seqs_assoc_l_res = compare_tm_const_pair_list vis_seqs_assoc_l exp_vis_seqs_assoc_l in
  (*Test method "reduce_rels"*)
  let rels_assoc_l3 = reduce_rels rels_assoc_l2 (init_visited_seqs_assoc_list rels_assoc_l2) in
  let exp_rels_assoc_l3 = [(seq1,[exp_upd_seqm_length])] in
  let comp_rels_assoc_l3_res = compare_rels_assoc_list rels_assoc_l3 exp_rels_assoc_l3 in
  (*Test method "create_mf_matrix"*)
  let mf_matrix1 = create_mf_matrix rels_assoc_l3 in
  let mf_row1 = init_mf_row in
  let upd_mf_row11 = List.remove_assoc "length" mf_row1 in
  let upd_mf_row12 = ("length",-1)::upd_mf_row11 in
  let comp_mf_matrix1_res = compare_mf_matrix_count mf_matrix1 [upd_mf_row12] in
  (*Run method "Frequencies.translate_mf_assoc_list" - tested in Frequencies*)
  let mf_matrix2 = Frequencies.translate_mf_assoc_list mf_matrix1 in (*TODO: Mock mf_matrix2 instead? Also in above tests?*)
  (*Mock algorithm step - tested in Dssa*)
  let selected_dss = [[0]] in
  (*Test method "connect_seqs_w_sel_dss"*)
  let sel_dss_assoc_l = connect_seqs_w_sel_dss selected_dss rels_assoc_l3 in
  let exp_sel_dss_assoc_l = [(seq1,0);(exp_upd_seqm_length,0)] in
  let comp_sel_dss_assoc_l_res = compare_tm_const_pair_list sel_dss_assoc_l exp_sel_dss_assoc_l in
  (*Test method "update_ast_w_sel_dss"*)
  let upd_ast = update_ast_w_sel_dss ast sel_dss_assoc_l false in
  let upd_seq1 =
    TmSeq((create_mock_ti (get_mock_tyseq_int) (us"seq1_fi1")),
          us"int",
          TmList([]),
          SeqList(Linkedlist.from_list [var_x]),
          0) in
  let upd_seqm_length =
    TmSeqMethod((create_mock_ti (get_mock_tyarrow_tyseq_int_gint) (us"seqm_length_fi1")),
                us"length",
                SeqFunNone,
                [],
                0,
                0,
                true) in
  let upd_app4 =
    TmApp((create_mock_ti (get_mock_gint) (us"app4_fi1")),
          upd_seqm_length,
          upd_seq1) in
  let upd_app5 =
    TmApp((create_mock_ti (get_mock_gint) (us"app5_fi1")),
          lam_s,
          upd_app4) in
  let upd_if1 =
    TmIfexp((create_mock_ti (get_mock_gint) (us"if1_fi1")),
            app7,
            upd_app5,
            app3) in
  let upd_lam_x =
    TmLam((create_mock_ti (get_mock_tyarrow_gint_gint) (us"lam_x_fi1")),
          us"x",
          get_mock_gint,
          upd_if1) in
  let upd_lam_fix_test =
    TmLam((create_mock_ti (get_mock_tyarrow_tyarrow_gint_gint_gint_gint) (us"lam_fix_test_fi1")),
          us"fix_test",
          get_mock_tyarrow_gint_gint,
          upd_lam_x) in
  let upd_app8 =
    TmApp((create_mock_ti (get_mock_gint) (us"app8_fi1")),
          TmFix(create_mock_ti (get_mock_gvoid) (us"app8_fi2")),
          upd_lam_fix_test) in
  let upd_app9 =
    TmApp((create_mock_ti (get_mock_gvoid) (us"app9_fi1")),
          lam_fix_test2,
          upd_app8) in
  let exp_upd_ast = upd_app9 in
  let comp_upd_ast_res = compare_asts upd_ast exp_upd_ast in
  (*Handle complete test result*)
  let test_res = comp_rels_res && comp_seqs_res && comp_seq_cons_res && comp_rels_assoc_l1_res && comp_rels_assoc_l2_res && comp_vis_seqs_assoc_l_res && comp_rels_assoc_l3_res && comp_mf_matrix1_res && comp_sel_dss_assoc_l_res && comp_upd_ast_res in
  let _ = Printf.printf "Test process steps 7: %s\n" (get_test_res_string test_res) in
  true
