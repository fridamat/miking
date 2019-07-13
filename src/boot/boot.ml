(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   boot.ml is the main entry point for first stage of the
   bootstrapped Miking compiler. The bootstapper is interpreted and
   implemented in OCaml. Note that the Miking bootstrapper
   only implements a subset of the Ragnar language.
*)


open Utils
open Ustring.Op
open Printf
open Ast
open Msg
open Pprint
open Linkedlist


let prog_argv = ref []          (* Argv for the program that is executed *)

(* Debug options *)
let enable_debug_eval = false
let enable_debug_eval_env = false
let enable_debug_after_parse = false
let enable_debug_after_debruijn = false
let enable_debug_after_erase = false

(* Evaluation of atoms. This is changed depending on the DSL *)
let empty_eval_atom fi id tms v = v
let eval_atom = ref empty_eval_atom


(* Traditional map function on unified collection (UC) types *)
let rec ucmap f uc = match uc with
  | UCLeaf(tms) -> UCLeaf(List.map f tms)
  | UCNode(uc1,uc2) -> UCNode(ucmap f uc1, ucmap f uc2)


(* Print out error message when a unit test fails *)
let unittest_failed fi t1 t2=
  uprint_endline
    (match fi with
    | Info(filename,l1,_,_,_) -> us"\n ** Unit test FAILED on line " ^.
        us(string_of_int l1) ^. us" **\n    LHS: " ^. (pprint true t1) ^.
        us"\n    RHS: " ^. (pprint true t2)
    | NoInfo -> us"Unit test FAILED ")

(* Add pattern variables to environment. Used in the debruijn function *)
let rec patvars env pat =
  match pat with
  | PatIdent(_,x) -> VarTm(x)::env
  | PatChar(_,_) -> env
  | PatUC(fi,p::ps,o,u) -> patvars (patvars env p) (PatUC(fi,ps,o,u))
  | PatUC(fi,[],o,u) -> env
  | PatBool(_,_) -> env
  | PatInt(_,_) -> env
  | PatConcat(_,p1,p2) -> patvars (patvars env p1) p2


(* Convert a term into de Bruijn indices. Note that both type variables
   and term variables are converted. The environment [env] is a list
   type [vartype], indicating if it is a type variable (VarTy(x)) or
   a term variable (VarTm(x)). *)
let rec debruijn env t =
  let rec debruijnTy env ty =
    (match ty with
    | TyGround(fi,gty) -> ty
    | TyArrow(fi,ty1,ty2) -> TyArrow(fi,debruijnTy env ty1,debruijnTy env ty2)
    | TyVar(fi,x,_) ->
      let rec find env n =
        (match env with
        | VarTy(y)::ee -> if y =. x then n else find ee (n+1)
        | VarTm(y)::ee -> find ee (n+1)
        | [] -> raise_error fi ("Unknown type variable '" ^ Ustring.to_utf8 x ^ "'"))
      in TyVar(fi,x,find env 0)
    | TyAll(fi,x,kind,ty1) -> TyAll(fi,x,kind, debruijnTy (VarTy(x)::env) ty1)
    | TyLam(fi,x,kind,ty1) -> TyLam(fi,x,kind, debruijnTy (VarTy(x)::env) ty1)
    | TyApp(fi,ty1,ty2) -> TyApp(fi, debruijnTy env ty1, debruijnTy env ty2)
    | TyDyn -> TyDyn
    | TySeq(seq_ty,id) -> TySeq(seq_ty,id)
    | TySeqMethod(i_ty,r_ty) -> TySeqMethod(i_ty,r_ty)
    )
  in
  let rec debruijn_list env l =
    (match l with
     | [] -> []
     | hd::tl -> (debruijn env hd)::(debruijn_list env tl))
  in
  match t with
  | TmVar(ti,x,_,_) ->
    let rec find env n =
      (match env with
       | VarTm(y)::ee -> if y =. x then n else find ee (n+1)
       | VarTy(y)::ee -> find ee (n+1)
       | [] -> raise_error ti.fi ("Unknown variable '" ^ Ustring.to_utf8 x ^ "'"))
    in TmVar(ti,x,find env 0,false)
  | TmLam(ti,x,ty,t1) -> TmLam(ti,x,debruijnTy env ty,debruijn (VarTm(x)::env) t1)
  | TmClos(ti,x,ty,t1,env1,_) -> failwith "Closures should not be available."
  | TmApp(ti,t1,t2) -> TmApp(ti,debruijn env t1,debruijn env t2)
  | TmConst(_,_) -> t
  | TmFix(_) -> t
  | TmTyLam(ti,x,kind,t1) -> TmTyLam(ti,x,kind,debruijn (VarTy(x)::env) t1)
  | TmTyApp(ti,t1,ty1) -> TmTyApp(ti,debruijn env t1, debruijnTy env ty1)
  | TmIfexp(ti,cnd,thn,els) -> TmIfexp(ti, debruijn env cnd, debruijn env thn, debruijn env els)
  | TmSeq(ti,ty_id,seq_ty,ds_choice,clist,cseq) -> TmSeq(ti,ty_id,seq_ty,ds_choice,TmList(debruijn_list env (get_list_from_tm_list clist)),cseq)
  | TmSeqMethod(ti,ds_choice,fun_name,args,arg_index) ->
    TmSeqMethod(ti,ds_choice,fun_name,(debruijn_list env args),arg_index)
  | TmChar(_,_) -> t
  | TmUC(ti,uct,o,u) -> TmUC(ti, UCLeaf(List.map (debruijn env) (uct2list uct)),o,u)
  | TmUtest(ti,t1,t2,tnext)
      -> TmUtest(ti,debruijn env t1,debruijn env t2,debruijn env tnext)
  | TmMatch(ti,t1,cases) ->
      TmMatch(ti,debruijn env t1,
               List.map (fun (Case(fi,pat,tm)) ->
                 Case(fi,pat,debruijn (patvars env pat) tm)) cases)
  | TmNop -> t

let compare_tm_terms tm1 tm2 =
  match tm1, tm2 with
  | TmConst(_,CInt(n1)), TmConst(_,CInt(n2)) -> (n1 = n2)
  | _ -> false

let rec compare_linked_lists ll1 ll2 i =
  if (i = Linkedlist.length ll1) && (i = Linkedlist.length ll2) then
    true
  else if (i = Linkedlist.length ll1) || (i = Linkedlist.length ll2) then
    false
  else if (compare_tm_terms (Linkedlist.nth ll1 i) (Linkedlist.nth ll2 i)) then
    compare_linked_lists ll1 ll2 (i+1)
  else
    false

let compare_sequences seq1 seq2 =
  match seq1, seq2 with
  | SeqList(ll1), SeqList(ll2) ->
    compare_linked_lists ll1 ll2 0
  | SeqNone, SeqNone -> true
  | _ -> failwith "Sequence not implemented."

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
  (*TODO: Add more types of lists*)
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
     | TmSeq(_,_,_,_,tm_l1,_), TmSeq(_,_,_,_,tm_l2,_) ->
       (*TODO: Is it enough to compare the tmls?*)
       compare_term_lists (get_list_from_tm_list tm_l1) (get_list_from_tm_list tm_l2)
     | TmSeqMethod(_,_,fun_name1,_,_), TmSeqMethod(_,_,fun_name2,_,_) ->
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

(* Check if two value terms are equal *)
let rec val_equal v1 v2 =
  match v1,v2 with
  | TmChar(_,n1),TmChar(_,n2) -> n1 = n2
  | TmConst(_,c1),TmConst(_,c2) -> c1 = c2
  | TmUC(_,t1,o1,u1),TmUC(_,t2,o2,u2) ->
      let rec eql lst1 lst2 = match lst1,lst2 with
        | l1::ls1,l2::ls2 when val_equal l1 l2 -> eql ls1 ls2
        | [],[] -> true
        | _ -> false
      in o1 = o2 && u1 = u2 && eql (uct2revlist t1) (uct2revlist t2)
  | TmNop,TmNop -> true
  | TmSeq(_,_,_,_,tml1,seq1), TmSeq(_,_,_,_,tml2,seq2) ->
    compare_sequences seq1 seq2
  | _ -> false

let ustring2uctstring s =
  let ls = List.map (fun i -> TmChar({ety=None; fi=NoInfo},i)) (ustring2list s) in
  TmUC({ety=None;fi =NoInfo},UCLeaf(ls),UCOrdered,UCMultivalued)


(* Update all UC to have the form of lists *)
let rec make_tm_for_match tm =
  let rec mklist uc acc =
    match uc with
    | UCNode(uc1,uc2) -> (mklist uc2 (mklist uc1 acc))
    | UCLeaf(lst) -> (List.map make_tm_for_match lst)::acc
  in
  let rec mkuclist lst acc =
    match lst with
    | x::xs -> mkuclist xs (UCNode(UCLeaf(x),acc))
    | [] -> acc
  in
  match tm with
  | TmUC(ti,uc,o,u) ->
    TmUC(ti,mkuclist (mklist uc []) (UCLeaf([])),o,u)
  | _ -> tm

(* Check if a UC struct has zero length *)
let rec uctzero uct =
  match uct with
  | UCNode(n1,n2) -> (uctzero n1) && (uctzero n2)
  | UCLeaf([]) -> true
  | UCLeaf(_) -> false


(* Matches a pattern against a value and returns a new environment
   Notes:
    - final is used to detect if a sequence be checked to be complete or not *)
let rec eval_match env pat t final =
    match pat,t with
  | PatIdent(_,x1),v -> Some(v::env,TmNop)
  | PatChar(_,c1),TmChar(_,c2) -> if c1 = c2 then Some(env,TmNop) else None
  | PatChar(_,_),_ -> None
  | PatUC(fi1,p::ps,o1,u1),TmUC(ti2,UCLeaf(t::ts),o2,u2) ->
    (match eval_match env p t true with
    | Some(env,_) ->
      eval_match env (PatUC(fi1,ps,o1,u1)) (TmUC(ti2,UCLeaf(ts),o2,u2)) final
    | None -> None)
  | PatUC(fi1,p::ps,o1,u1),TmUC(ti2,UCLeaf([]),o2,u2) -> None
  | PatUC(fi1,p::ps,o1,u1),TmUC(ti2,UCNode(UCLeaf(t::ts),t2),o2,u2) ->
    (match eval_match env p t true with
    | Some(env,_) ->
      eval_match env (PatUC(fi1,ps,o1,u1))
        (TmUC(ti2,UCNode(UCLeaf(ts),t2),o2,u2)) final
    | None -> None)
  | PatUC(fi1,p::ps,o1,u1),TmUC(ti2,UCNode(UCLeaf([]),t2),o2,u2) ->
      eval_match env pat (TmUC(ti2,t2,o2,u2)) final
  | PatUC(fi1,[],o1,u1),TmUC(ti2,uct,_,_) when uctzero uct && final -> Some(env,TmNop)
  | PatUC(fi1,[],o1,u1),t when not final-> Some(env,t)
  | PatUC(fi1,lst,o1,u2),t -> None
  | PatBool(_,b1),TmConst(_,CBool(b2)) -> if b1 = b2 then Some(env,TmNop) else None
  | PatBool(_,_),_ -> None
  | PatInt(fi,i1),TmConst(_,CInt(i2)) -> if i1 = i2 then Some(env,TmNop) else None
  | PatInt(_,_),_ -> None
  | PatConcat(_,PatIdent(_,x),p2),_ ->
      failwith "Pattern variable first is not part of Ragnar--"
  | PatConcat(_,p1,p2),t1 ->
    (match eval_match env p1 t1 false with
    | Some(env,t2) -> eval_match env p2 t2 (final && true)
    | None -> None)

let fail_constapp fi = raise_error fi "Incorrect application "

(* Debug function used in the eval function *)
let debug_eval env t =
  if enable_debug_eval then
    (printf "\n-- eval -- \n";
     uprint_endline (pprint true t);
     if enable_debug_eval_env then
        uprint_endline (pprint_env env))
  else ()

(* Debug template function. Used below*)
let debug_after t flag text=
  if flag then
    (printf "\n-- %s --  \n" text;
     uprint_endline (pprint true t);
     t)
  else t


(* Debug function used after specific tasks *)
let debug_after_parse t = debug_after t enable_debug_after_parse "After parsing"
let debug_after_debruijn t = debug_after t enable_debug_after_debruijn "After debruijn"
let debug_after_erase t = debug_after t enable_debug_after_erase "After erase"


(* Mapping between named builtin functions (intrinsics) and the
   correspond constants *)
let builtin =
  [("not",Cnot);("and",Cand(None));("or",Cor(None));
   ("addi",Caddi(None));("subi",Csubi(None));("muli",Cmuli(None));
   ("divi",Cdivi(None));("modi",Cmodi(None));("negi",Cnegi);
   ("lti",Clti(None));("leqi",Cleqi(None));("gti",Cgti(None));("geqi",Cgeqi(None));
   ("eqi",Ceqi(None));("neqi",Cneqi(None));
   ("slli",Cslli(None));("srli",Csrli(None));("srai",Csrai(None));
   ("addf",Caddf(None));("subf",Csubf(None));("mulf",Cmulf(None));
   ("divf",Cdivf(None));("negf",Cnegf);
   ("add",Cadd(TNone));("sub",Csub(TNone));("mul",Cmul(TNone));
   ("div",Cdiv(TNone));("neg",Cneg);
   ("dstr",CDStr);("dprint",CDPrint);("print",CPrint);("argv",CArgv);
   ("concat",CConcat(None))]



(* Evaluates a constant application. This is the standard delta function
   delta(c,v) with the exception that it returns an expression and not
   a value. This is why the returned value is evaluated in the eval() function.
   The reason for this is that if-expressions return expressions
   and not values. *)
let delta c v  =
    match c,v with
    (* MCore boolean intrinsics *)
    | CBool(_),t -> fail_constapp (tm_info t)

    | Cnot,TmConst(ti,CBool(v)) -> TmConst(ti,CBool(not v))
    | Cnot,t -> fail_constapp (tm_info t)

    | Cand(None),TmConst(ti,CBool(v)) -> TmConst(ti,Cand(Some(v)))
    | Cand(Some(v1)),TmConst(ti,CBool(v2)) -> TmConst(ti,CBool(v1 && v2))
    | Cand(None),t | Cand(Some(_)),t  -> fail_constapp (tm_info t)

    | Cor(None),TmConst(ti,CBool(v)) -> TmConst(ti,Cor(Some(v)))
    | Cor(Some(v1)),TmConst(ti,CBool(v2)) -> TmConst(ti,CBool(v1 || v2))
    | Cor(None),t | Cor(Some(_)),t  -> fail_constapp (tm_info t)

    (* MCore integer intrinsics *)
    | CInt(_),t -> fail_constapp (tm_info t)

    | Caddi(None),TmConst(ti,CInt(v)) -> TmConst(ti,Caddi(Some(v)))
    | Caddi(Some(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CInt(v1 + v2))
    | Caddi(None),t | Caddi(Some(_)),t  -> fail_constapp (tm_info t)

    | Csubi(None),TmConst(ti,CInt(v)) -> TmConst(ti,Csubi(Some(v)))
    | Csubi(Some(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CInt(v1 - v2))
    | Csubi(None),t | Csubi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cmuli(None),TmConst(ti,CInt(v)) -> TmConst(ti,Cmuli(Some(v)))
    | Cmuli(Some(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CInt(v1 * v2))
    | Cmuli(None),t | Cmuli(Some(_)),t  -> fail_constapp (tm_info t)

    | Cdivi(None),TmConst(ti,CInt(v)) -> TmConst(ti,Cdivi(Some(v)))
    | Cdivi(Some(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CInt(v1 / v2))
    | Cdivi(None),t | Cdivi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cmodi(None),TmConst(ti,CInt(v)) -> TmConst(ti,Cmodi(Some(v)))
    | Cmodi(Some(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CInt(v1 mod v2))
    | Cmodi(None),t | Cmodi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cnegi,TmConst(ti,CInt(v)) -> TmConst(ti,CInt((-1)*v))
    | Cnegi,t -> fail_constapp (tm_info t)

    | Clti(None),TmConst(ti,CInt(v)) -> TmConst(ti,Clti(Some(v)))
    | Clti(Some(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CBool(v1 < v2))
    | Clti(None),t | Clti(Some(_)),t  -> fail_constapp (tm_info t)

    | Cleqi(None),TmConst(ti,CInt(v)) -> TmConst(ti,Cleqi(Some(v)))
    | Cleqi(Some(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CBool(v1 <= v2))
    | Cleqi(None),t | Cleqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cgti(None),TmConst(ti,CInt(v)) -> TmConst(ti,Cgti(Some(v)))
    | Cgti(Some(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CBool(v1 > v2))
    | Cgti(None),t | Cgti(Some(_)),t  -> fail_constapp (tm_info t)

    | Cgeqi(None),TmConst(ti,CInt(v)) -> TmConst(ti,Cgeqi(Some(v)))
    | Cgeqi(Some(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CBool(v1 >= v2))
    | Cgeqi(None),t | Cgeqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Ceqi(None),TmConst(ti,CInt(v)) -> TmConst(ti,Ceqi(Some(v)))
    | Ceqi(Some(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CBool(v1 = v2))
    | Ceqi(None),t | Ceqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cneqi(None),TmConst(ti,CInt(v)) -> TmConst(ti,Cneqi(Some(v)))
    | Cneqi(Some(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CBool(v1 <> v2))
    | Cneqi(None),t | Cneqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cslli(None),TmConst(ti,CInt(v)) -> TmConst(ti,Cslli(Some(v)))
    | Cslli(Some(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CInt(v1 lsl v2))
    | Cslli(None),t | Cslli(Some(_)),t  -> fail_constapp (tm_info t)

    | Csrli(None),TmConst(ti,CInt(v)) -> TmConst(ti,Csrli(Some(v)))
    | Csrli(Some(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CInt(v1 lsr v2))
    | Csrli(None),t | Csrli(Some(_)),t  -> fail_constapp (tm_info t)

    | Csrai(None),TmConst(ti,CInt(v)) -> TmConst(ti,Csrai(Some(v)))
    | Csrai(Some(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CInt(v1 asr v2))
    | Csrai(None),t | Csrai(Some(_)),t  -> fail_constapp (tm_info t)

    (* MCore intrinsic: Floating-point number constant and operations *)
    | CFloat(_),t -> fail_constapp (tm_info t)

    | Caddf(None),TmConst(ti,CFloat(v)) -> TmConst(ti,Caddf(Some(v)))
    | Caddf(Some(v1)),TmConst(ti,CFloat(v2)) -> TmConst(ti,CFloat(v1 +. v2))
    | Caddf(None),t | Caddf(Some(_)),t  -> fail_constapp (tm_info t)

    | Csubf(None),TmConst(ti,CFloat(v)) -> TmConst(ti,Csubf(Some(v)))
    | Csubf(Some(v1)),TmConst(ti,CFloat(v2)) -> TmConst(ti,CFloat(v1 -. v2))
    | Csubf(None),t | Csubf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cmulf(None),TmConst(ti,CFloat(v)) -> TmConst(ti,Cmulf(Some(v)))
    | Cmulf(Some(v1)),TmConst(ti,CFloat(v2)) -> TmConst(ti,CFloat(v1 *. v2))
    | Cmulf(None),t | Cmulf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cdivf(None),TmConst(ti,CFloat(v)) -> TmConst(ti,Cdivf(Some(v)))
    | Cdivf(Some(v1)),TmConst(ti,CFloat(v2)) -> TmConst(ti,CFloat(v1 /. v2))
    | Cdivf(None),t | Cdivf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cnegf,TmConst(ti,CFloat(v)) -> TmConst(ti,CFloat((-1.0)*.v))
    | Cnegf,t -> fail_constapp (tm_info t)

    (* Mcore intrinsic: Polymorphic integer and floating-point numbers *)

    | Cadd(TNone),TmConst(ti,CInt(v)) -> TmConst(ti,Cadd(TInt(v)))
    | Cadd(TNone),TmConst(ti,CFloat(v)) -> TmConst(ti,Cadd(TFloat(v)))
    | Cadd(TInt(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CInt(v1 + v2))
    | Cadd(TFloat(v1)),TmConst(ti,CFloat(v2)) -> TmConst(ti,CFloat(v1 +. v2))
    | Cadd(TFloat(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CFloat(v1 +. (float_of_int v2)))
    | Cadd(TInt(v1)),TmConst(ti,CFloat(v2)) -> TmConst(ti,CFloat((float_of_int v1) +. v2))
    | Cadd(_),t -> fail_constapp (tm_info t)

    | Csub(TNone),TmConst(ti,CInt(v)) -> TmConst(ti,Csub(TInt(v)))
    | Csub(TNone),TmConst(ti,CFloat(v)) -> TmConst(ti,Csub(TFloat(v)))
    | Csub(TInt(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CInt(v1 - v2))
    | Csub(TFloat(v1)),TmConst(ti,CFloat(v2)) -> TmConst(ti,CFloat(v1 -. v2))
    | Csub(TFloat(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CFloat(v1 -. (float_of_int v2)))
    | Csub(TInt(v1)),TmConst(ti,CFloat(v2)) -> TmConst(ti,CFloat((float_of_int v1) -. v2))
    | Csub(_),t -> fail_constapp (tm_info t)

    | Cmul(TNone),TmConst(ti,CInt(v)) -> TmConst(ti,Cmul(TInt(v)))
    | Cmul(TNone),TmConst(ti,CFloat(v)) -> TmConst(ti,Cmul(TFloat(v)))
    | Cmul(TInt(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CInt(v1 * v2))
    | Cmul(TFloat(v1)),TmConst(ti,CFloat(v2)) -> TmConst(ti,CFloat(v1 *. v2))
    | Cmul(TFloat(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CFloat(v1 *. (float_of_int v2)))
    | Cmul(TInt(v1)),TmConst(ti,CFloat(v2)) -> TmConst(ti,CFloat((float_of_int v1) *. v2))
    | Cmul(_),t -> fail_constapp (tm_info t)

    | Cdiv(TNone),TmConst(ti,CInt(v)) -> TmConst(ti,Cdiv(TInt(v)))
    | Cdiv(TNone),TmConst(ti,CFloat(v)) -> TmConst(ti,Cdiv(TFloat(v)))
    | Cdiv(TInt(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CInt(v1 / v2))
    | Cdiv(TFloat(v1)),TmConst(ti,CFloat(v2)) -> TmConst(ti,CFloat(v1 /. v2))
    | Cdiv(TFloat(v1)),TmConst(ti,CInt(v2)) -> TmConst(ti,CFloat(v1 /. (float_of_int v2)))
    | Cdiv(TInt(v1)),TmConst(ti,CFloat(v2)) -> TmConst(ti,CFloat((float_of_int v1) /. v2))
    | Cdiv(_),t -> fail_constapp (tm_info t)

    | Cneg,TmConst(ti,CFloat(v)) -> TmConst(ti,CFloat((-1.0)*.v))
    | Cneg,TmConst(ti,CInt(v)) -> TmConst(ti,CInt((-1)*v))
    | Cneg,t -> fail_constapp (tm_info t)

    (* MCore debug and stdio intrinsics *)
    | CDStr, t -> ustring2uctstring (pprint true t)
    | CDPrint, t -> uprint_endline (pprint true t);TmNop
    | CPrint, t ->
      (match t with
      | TmUC(_,uct,_,_) ->
        uct2list uct |> uc2ustring |> list2ustring |> Ustring.to_utf8
      |> printf "%s"; TmNop
      | _ -> raise_error (tm_info t) "Cannot print value with this type")
    | CArgv,_ ->
      let lst = List.map (fun x -> ustring2uctm {ety = None; fi = NoInfo} (us x)) (!prog_argv)
      in TmUC({ety = None; fi = NoInfo},UCLeaf(lst),UCOrdered,UCMultivalued)
    | CConcat(None),t -> TmConst({ety = None; fi = NoInfo},CConcat((Some t)))
    | CConcat(Some(TmUC(l,t1,o1,u1))),TmUC(_,t2,o2,u2)
      when o1 = o2 && u1 = u2 -> TmUC(l,UCNode(t1,t2),o1,u1)
    | CConcat(Some(tm1)),TmUC(l,t2,o2,u2) -> TmUC(l,UCNode(UCLeaf([tm1]),t2),o2,u2)
    | CConcat(Some(TmUC(l,t1,o1,u1))),tm2 -> TmUC(l,UCNode(t1,UCLeaf([tm2])),o1,u1)
    | CConcat(Some(_)),t -> fail_constapp (tm_info t)

    (* Atom - an untyped lable that can be used to implement
       domain specific constructs *)
    | CAtom(id,tms),t -> !eval_atom (tm_info t) id tms t



(* Optimize away constant applications (mul with 0 or 1, add with 0 etc.) *)
let optimize_const_app fi v1 v2 =
  match v1,v2 with
  (*|   0 * x  ==>  0   |*)
  | TmConst(ti,Cmuli(Some(0))),v2 -> TmConst(ti,CInt(0))
  (*|   1 * x  ==>  x   |*)
  | TmConst(_,Cmuli(Some(1))),v2 -> v2
  (*|   0 + x  ==>  x   |*)
  | TmConst(_,Caddi(Some(0))),v2 -> v2
  (*|   0 * x  ==>  0   |*)
  | TmApp(_,TmConst(_,Cmuli(None)),TmConst(ti,CInt(0))),vv1 -> TmConst(ti,CInt(0))
  (*|   1 * x  ==>  x   |*)
  | TmApp(_,TmConst(_,Cmuli(None)),TmConst(_,CInt(1))),vv1 -> vv1
  (*|   0 + x  ==>  x   |*)
  | TmApp(_,TmConst(_,Caddi(None)),TmConst(_,CInt(0))),vv1 -> vv1
  (*|   x * 0  ==>  0   |*)
  | TmApp(_,TmConst(_,Cmuli(None)),vv1),TmConst(ti,CInt(0)) -> TmConst(ti,CInt(0))
  (*|   x * 1  ==>  x   |*)
  | TmApp(_,TmConst(_,Cmuli(None)),vv1),TmConst(_,CInt(1)) -> vv1
  (*|   x + 0  ==>  x   |*)
  | TmApp(_,TmConst(_,Caddi(None)),vv1),TmConst(_,CInt(0)) -> vv1
  (*|   x - 0  ==>  x   |*)
  | TmApp(_,TmConst(_,Csubi(None)),vv1),TmConst(_,CInt(0)) -> vv1
  (*|   x op y  ==>  res(x op y)   |*)
  | TmConst(_,c1),(TmConst(_,c2) as tt)-> delta c1 tt
  (* No optimization *)
  | vv1,vv2 -> TmApp({ety = Some TyDyn; fi},vv1,vv2)

(*eval helper methods*)
let get_seq_from_list tml seq =
  match tml, seq with
  | TmList(l), SeqList(_) -> SeqList(Linkedlist.from_list l)
  | _ -> failwith "Sequence type not implemented."

let rec add_evaluated_term_to_args args term =
  match args with
  | [] -> term::[]
  | hd::tl -> hd::(add_evaluated_term_to_args tl term)

let get_arg_types_length_dummy fi fun_name =
  match Ustring.to_utf8 fun_name with
  | "length" -> 0
  | "append" -> 1
  | "add" -> 1
  | "nth" -> 1
  | "push" -> 1
  | _ -> raise_error fi "Sequence method not implemented."

let get_last_arg_index fun_name =
  (*TODO: Check length of arg types in sequence function table*)
  get_arg_types_length_dummy fun_name

let call_length_method ti args =
  match args with
  | [TmSeq(_,ty_id,seq_ty,ds_choice,clist,cseq)] ->
    (match cseq with
     | SeqList(ll) ->
       TmConst(ti,CInt(Linkedlist.length ll))
     | _ -> raise_error ti.fi "No such data structure type.")
  | _ -> raise_error ti.fi "Sequence method not implemented."

let call_append_method ti args =
  match args with
  | [TmSeq(ti1,ty_id1,seq_ty1,ds_choice1,tmlist1,tmseq1); TmSeq(ti2,ty_id2,seq_ty2,ds_choice2,tmlist2,tmseq2)] ->
    (match tmseq1,tmseq2 with
     | SeqList(ll1), SeqList(ll2) ->
       let new_sequence = Linkedlist.append ll1 ll2 in
       let res = TmSeq(ti1,ty_id1,seq_ty1,ds_choice1,TmList([]),SeqList(new_sequence)) in
       res
     | _ -> raise_error ti.fi "No such data structure type.")
  | _ -> raise_error ti.fi "Sequence method2 not implemented."


let call_seq_method ti ds_choice fun_name args =
  (*TODO: Open ds_choice for method*)
  (*TODO: Check arg types against sequence function table*)
  (*TODO: Check that number of arguments are correct (earlier?)*)
  match Ustring.to_utf8 fun_name with
  | "length" -> call_length_method ti args
  | "append" ->
    let res = call_append_method ti args in
    res
  | _ -> raise_error ti.fi "Sequence method3 not implemented."

(* Main evaluation loop of a term. Evaluates using big-step semantics *)
let rec eval env t =
  let rec eval_tmlist env tm_l =
    (match tm_l with
     | TmList([]) -> []
     | TmList(hd::tl) -> (eval env hd)::(eval_tmlist env (TmList(tl)))
    ) in
  debug_eval env t;
  match t with
  (* Variables using debruijn indices. Need to evaluate because fix point. *)
  | TmVar(ti,x,n,_) -> eval env (List.nth env n)
  (* Lambda and closure conversions *)
  | TmLam(ti,x,ty,t1) -> TmClos(ti,x,ty,t1,env,false)
  | TmClos(ti,x,_,t1,env2,_) -> t
  (* Application *)
  | TmApp(ti,t1,t2) ->
      (match eval env t1 with
       (* Closure application *)
        | TmClos(ti,x,_,t3,env2,_) ->
          eval ((eval env t2)::env2) t3
       (* Constant application using the delta function *)
       | TmConst(ti,c) -> delta c (eval env t2)
       (* Fix *)
       | TmFix(ti) ->
         (match eval env t2 with
         | TmClos(fi,x,_,t3,env2,_) as tt -> eval ((TmApp(ti,TmFix(ti),tt))::env2) t3
         | _ -> failwith "Incorrect CFix")
       | TmSeqMethod(ti,ds_choice,fun_name,args,arg_index) ->
         let updated_args = add_evaluated_term_to_args args (eval env t2) in
         let last_arg_index = get_last_arg_index ti.fi fun_name in
         if arg_index == last_arg_index then
           let res = call_seq_method ti ds_choice fun_name updated_args in
           res
         else if arg_index < last_arg_index then
           TmSeqMethod(ti,ds_choice,fun_name,updated_args,(arg_index+1))
         else
           raise_error ti.fi "Argument index is out of bounds."
       | _ -> raise_error ti.fi "Application to a non closure value.")
  (* Constant *)
  | TmConst(_,_) | TmFix(_) -> t
  (* System F terms *)
  | TmTyLam(ti,_,_,_) | TmTyApp(ti,_,_) -> failwith "System F terms should not exist (4)"
  (* If expression *)
  | TmIfexp(ti,cnd,thn,els) ->
    (match eval env cnd with
     | TmConst(_,CBool(b)) ->
       if b then
         eval env thn
       else
         eval env els
     | _ -> raise_error ti.fi "Condition in if-expression not a bool.")
  (* Sequence constructor *)
  | TmSeq(fi,ty_id,seq_ty,ds_choice,tmlist,tmseq) ->
    (match tmseq with
    | SeqNone ->
      let new_tmlist = TmList(eval_tmlist env tmlist) in
      let new_tmseq = get_seq_from_list new_tmlist tmseq in
      TmSeq(fi,ty_id,seq_ty,ds_choice,new_tmlist,new_tmseq)
    | _ -> t)
  (* Sequence method*)
  | TmSeqMethod(_,_,_,_,_) -> t
  (* The rest *)
  | TmChar(_,_) -> t
  | TmUC(ti,uct,o,u) -> TmUC(ti,ucmap (eval env) uct,o,u)
  | TmUtest(ti,t1,t2,tnext) ->
    if !utest then begin
      let (v1,v2) = ((eval env t1),(eval env t2)) in
        if val_equal v1 v2 then
         (printf "."; utest_ok := !utest_ok + 1)
       else (
        unittest_failed ti.fi v1 v2;
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
     end;
    eval env tnext
  | TmMatch(ti,t1,cases) -> (
     let v1 = make_tm_for_match (eval env t1) in
     let rec appcases cases =
       match cases with
       | Case(_,p,t)::cs ->
          (match eval_match env p v1 true with
         | Some(env,_) -> eval env t
         | None -> appcases cs)
       | [] -> raise_error ti.fi  "Match error"
     in
      appcases cases)
  | TmNop -> t

let check_if_seq ti =
  match Typesys.getType ti with
  | TySeq _ -> true
  | TySeqMethod(_,TySeq _) -> true
  | TyArrow(_,TySeq _, _) -> true
  | TyArrow(_,TySeqMethod(_,TySeq _), _) -> true
  | _ -> false

let get_fi_string_from_ti ti =
  match ti with
  | {fi} -> (Ustring.to_utf8 (info2str fi))

let find_rels_in_tmapp tm1 tm2 rels =
  (*TODO: Some cases below are duplicates if we don't want to distinguish between input and return types of methods*)
  match tm1, tm2, (check_if_seq tm1), (check_if_seq tm2), Typesys.getType tm1 with
  | TmLam(lam_ti,_,_,_), TmSeq(seq_ti,_,_,_,_,_), true, true, _ (*"let x = new sequence"*) ->
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
  | TmSeqMethod(seqm_ti,_,_,_,_), TmSeq(seq_ti,_,_,_,_,_), _, true, TySeqMethod(_,TySeq _) (*"seqmethod sequence" where the sequence is the first sequence argument to the method and hence the sequence decides the method's sequence INPUT and RETURN type*) ->
    (*Rel: return and input type of s1 = s2*)
    let new_rel = (tm1,tm2) in
    new_rel::rels
  | TmSeqMethod(seqm_ti,_,_,_,_), _, _, true, TySeqMethod(_,TySeq _) (*"seqmethod a" where a is the first argument of type sequence to the method and hence a decides the method's sequence INPUT and RETURN type*) ->
    (*Rel: return and input type of s1 = s2*)
    let new_rel = (tm1,tm2) in
    new_rel::rels
  | TmSeqMethod(seqm_ti,_,_,_,_), TmSeq(seq_ti,_,_,_,_,_), _, true, TySeqMethod _ (*"seqmethod sequence" where the sequence is the first sequence argument to the method and hence the sequence decides the method's sequence INPUT type, but not the return type since the return type of the method is not a sequence*) ->
    (*Rel: input type of s1 = s2*)
    let new_rel = (tm1,tm2) in
    new_rel::rels
  | TmSeqMethod(seqm_ti,_,_,_,_), _, _, true, TySeqMethod _ (*"seqmethod a" where a is the first argument of type sequence to the method and hence a decides the method's sequence INPUT type, but not the return type since the return type of the method is not a sequence*) ->
    (*Rel: input type of s1 = s2*)
    let new_rel = (tm1,tm2) in
    new_rel::rels
  | TmApp(app_ti,_,_), TmSeq(seq_ti,_,_,_,_,_), _, true, TySeqMethod _ (*"a1 sequence" where a1 is of type sequence method and sequence is an argument (but not the first) to it. The method will already have the sequence type set from its first argument, so its sequence type will decide the sequence type of the sequence.*) ->
    (*Rel: s2 = input type of s1*)
    let new_rel = (tm2,tm1) in
    new_rel::rels
  | TmApp(app_ti,_,_), _, _, true, TySeqMethod _ (*"a1 a2" where a1 is of type sequence method and a2 is of type sequence. The method will already have the sequence type set from its first argument, so its sequence type will decide the sequence type of a2.*) ->
    (*Rel: s2 = input type of s1*)
    let new_rel = (tm2,tm1) in
    new_rel::rels
  | _ -> rels

let rec traverse_AST_to_find_sequences t env rels seqs =
  let rec traverse_AST_list l l_env l_rels l_seqs =
    (match l with
     | [] -> (l_rels,l_seqs)
     | hd::tl ->
       let (l_rels1,l_seqs1) = traverse_AST_to_find_sequences hd l_env l_rels l_seqs in
       traverse_AST_list tl l_env l_rels1 l_seqs1
    ) in
  match t with
  | TmSeq(ti,_,_,_,tm_l,_) ->
    let seqs1 = t::seqs in
    traverse_AST_list (get_list_from_tm_list tm_l) env rels seqs1
  | TmNop -> (rels,seqs)
  | TmVar _ | TmChar _ | TmSeqMethod _ | TmFix _ | TmConst _ ->
    if check_if_seq t then
      (rels,t::seqs)
    else
      (rels,seqs)
  | TmLam(ti,_,_,tm) | TmClos(ti,_,_,tm,_,_) ->
    let (rels1,seqs1) =
      (if check_if_seq t then
         (rels,t::seqs)
       else
         (rels,seqs)
      ) in
    traverse_AST_to_find_sequences tm env rels1 seqs1
  | TmApp(ti,tm1,tm2) ->
    let rels1 = find_rels_in_tmapp tm1 tm2 rels in
    let (rels2,seqs1) = traverse_AST_to_find_sequences tm1 env rels1 seqs in
    traverse_AST_to_find_sequences tm2 env rels2 seqs1
  | TmUtest(ti,tm1,tm2,tm3) | TmIfexp(ti,tm1,tm2,tm3) ->
    let (rels1,seqs1) =
      (if check_if_seq t then
         (rels,t::seqs)
       else
         (rels,seqs)
      ) in
    let (rels2,seqs2) = traverse_AST_to_find_sequences tm1 env rels1 seqs1 in
    let (rels3,seqs3) = traverse_AST_to_find_sequences tm2 env rels2 seqs2 in
    traverse_AST_to_find_sequences tm3 env rels3 seqs3
  | TmMatch _ | TmUC _ | TmTyApp _ | TmTyLam _ ->
    failwith "Not implemented"

let rec print_seqs seqs =
  match seqs with
  | [] -> us"\n"
  | hd::tl ->
    us"\n- " ^. (Pprint.pprint false hd) ^. us"," ^. (print_seqs tl)

let rec print_rels rels =
  match rels with
  | [] -> us"\n"
  | (hd1,hd2)::tl ->
    us"\n- " ^. (Pprint.pprint false hd1) ^. us" = " ^. (Pprint.pprint false hd2) ^. us"," ^. (print_rels tl)

let eval_test typecheck env t =
  let _ = Printf.printf "The complete program is: %s \n" (Ustring.to_utf8 (Pprint.pprint false t)) in
  if typecheck then
    let (rels,seqs) = traverse_AST_to_find_sequences t env [] [] in
    let seqs_string = print_seqs seqs in
    let _ = Printf.printf "\nThe program points that are seqs are: %s of length %d" (Ustring.to_utf8 seqs_string) (List.length seqs) in
    let rels_string = print_rels rels in
    let _ = Printf.printf "\nThe relationships between seqs are: %s of length %d" (Ustring.to_utf8 rels_string) (List.length rels) in
    eval env t
  else
    eval env t

(* Main function for evaluation a function. Performs lexing, parsing
   and evaluation. Does not perform any type checking *)
let evalprog filename typecheck =
  if !utest then printf "%s: " filename;
  utest_fail_local := 0;
  let fs1 = open_in filename in
  let tablength = 8 in
  begin try
    Lexer.init (us filename) tablength;
    fs1 |> Ustring.lexing_from_channel
        |> Parser.main Lexer.main |> debug_after_parse
        |> debruijn (builtin |> List.split |> fst |> (List.map (fun x-> VarTm(us x))))
        |> debug_after_debruijn
        |> (if typecheck then Typesys.typecheck builtin else fun x -> x)
        (*TODO: Data structure selection*)
        |> Typesys.erase |> debug_after_erase
        (* TODO: Give the right types to built-ins *)
        |> eval_test typecheck (builtin |> List.split |> snd |> List.map (fun x -> TmConst({ety = None; fi = NoInfo},x)))
        |> fun _ -> ()

    with
    | Lexer.Lex_error m ->
      if !utest then (
        printf "\n%s" (Ustring.to_utf8 (Msg.message2str m));
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
      else
        fprintf stderr "%s\n" (Ustring.to_utf8 (Msg.message2str m))
    | Error m ->
      if !utest then (
        printf "\n%s" (Ustring.to_utf8 (Msg.message2str m));
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
      else
        fprintf stderr "%s\n" (Ustring.to_utf8 (Msg.message2str m))
    | Parsing.Parse_error ->
      if !utest then (
        printf "\n%s" (Ustring.to_utf8 (Msg.message2str (Lexer.parse_error_message())));
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
      else
        fprintf stderr "%s\n"
	(Ustring.to_utf8 (Msg.message2str (Lexer.parse_error_message())))
  end; close_in fs1;
  if !utest && !utest_fail_local = 0 then printf " OK\n" else printf "\n"


(* Define the file slash, to make it platform independent *)
let sl = if Sys.win32 then "\\" else "/"

(* Add a slash at the end "\\" or "/" if not already available *)
let add_slash s =
  if String.length s = 0 || (String.sub s (String.length s - 1) 1) <> sl
  then s ^ sl else s

(* Expand a list of files and folders into a list of file names *)
let files_of_folders lst = List.fold_left (fun a v ->
  if Sys.is_directory v then
    (Sys.readdir v
        |> Array.to_list
        |> List.filter (fun x -> not (String.length x >= 1 && String.get x 0 = '.'))
        |> List.map (fun x -> (add_slash v) ^ x)
        |> List.filter (fun x -> not (Sys.is_directory x))
    ) @ a
  else v::a
) [] lst

(* Iterate over all potential test files and run tests *)
let testprog lst typecheck =
    utest := true;
    let eprog name = evalprog name typecheck
    in
    (* Evaluate each of the programs in turn *)
    List.iter eprog (files_of_folders lst);

    (* Print out unit test results, if applicable *)
    if !utest_fail = 0 then
      printf "\nUnit testing SUCCESSFUL after executing %d tests.\n"
        (!utest_ok)
            else
      printf "\nERROR! %d successful tests and %d failed tests.\n"
        (!utest_ok) (!utest_fail)

(* Run program *)
let runprog name lst typecheck =
    prog_argv := lst;
    evalprog name typecheck


(* Print out main menu *)
let menu() =
  printf "Usage: boot [run|test] <files>\n";
  printf "\n"


(* Main function. Checks arguments and reads file names *)
let main =
  (* Check command  *)
  (match Array.to_list Sys.argv |> List.tl with

  (* Run tests on one or more files *)
  | "test"::lst | "t"::lst -> testprog lst false

  (* Run tests on one or more files, including type checking *)
  | "tytest"::lst -> testprog lst true

  (* Run one program with program arguments without typechecking *)
  | "tyrun"::name::lst -> runprog name lst true

  (* Run one program with program arguments without typechecking *)
  | "run"::name::lst | name::lst -> runprog name lst false



  (* Show the menu *)
  | _ -> menu())
