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
    )
  in
  let rec debruijn_list env l =
    (match l with
     | [] -> []
     | hd::tl -> (debruijn env hd)::(debruijn_list env tl))
  in
  match t with
  | TmVar(fi,x,_,_) ->
    let rec find env n =
      (match env with
       | VarTm(y)::ee -> if y =. x then n else find ee (n+1)
       | VarTy(y)::ee -> find ee (n+1)
       | [] -> raise_error fi ("Unknown variable '" ^ Ustring.to_utf8 x ^ "'"))
    in TmVar(fi,x,find env 0,false)
  | TmLam(fi,x,ty,t1) -> TmLam(fi,x,debruijnTy env ty,debruijn (VarTm(x)::env) t1)
  | TmClos(fi,x,ty,t1,env1,_) -> failwith "Closures should not be available."
  | TmApp(fi,t1,t2) -> TmApp(fi,debruijn env t1,debruijn env t2)
  | TmConst(_,_) -> t
  | TmFix(_) -> t
  | TmTyLam(fi,x,kind,t1) -> TmTyLam(fi,x,kind,debruijn (VarTy(x)::env) t1)
  | TmTyApp(fi,t1,ty1) -> TmTyApp(fi,debruijn env t1, debruijnTy env ty1)
  | TmIfexp(fi,cnd,thn,els) -> TmIfexp(fi, debruijn env cnd, debruijn env thn, debruijn env els)
  | TmSeq(fi,ty_id,ds_choice,clist,cseq) -> t (*TODO: Change if sequence can consist of terms*)
  | TmSeqMethod(fi,ds_choice,fun_name,args,arg_index) ->
    TmSeqMethod(fi,ds_choice,fun_name,(debruijn_list env args),arg_index)
  | TmChar(_,_) -> t
  | TmUC(fi,uct,o,u) -> TmUC(fi, UCLeaf(List.map (debruijn env) (uct2list uct)),o,u)
  | TmUtest(fi,t1,t2,tnext)
      -> TmUtest(fi,debruijn env t1,debruijn env t2,debruijn env tnext)
  | TmMatch(fi,t1,cases) ->
      TmMatch(fi,debruijn env t1,
               List.map (fun (Case(fi,pat,tm)) ->
                 Case(fi,pat,debruijn (patvars env pat) tm)) cases)
  | TmNop -> t


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
  | TmSeq(_,_,_,seq1,_), TmSeq(_,_,_,seq2,_) ->
    if seq1 = seq2 then
      true
    else
      false
  | _ -> false

let ustring2uctstring s =
  let ls = List.map (fun i -> TmChar(NoInfo,i)) (ustring2list s) in
  TmUC(NoInfo,UCLeaf(ls),UCOrdered,UCMultivalued)


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
  | TmUC(fi,uc,o,u) ->
    TmUC(fi,mkuclist (mklist uc []) (UCLeaf([])),o,u)
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
  | PatUC(fi1,p::ps,o1,u1),TmUC(fi2,UCLeaf(t::ts),o2,u2) ->
    (match eval_match env p t true with
    | Some(env,_) ->
      eval_match env (PatUC(fi1,ps,o1,u1)) (TmUC(fi2,UCLeaf(ts),o2,u2)) final
    | None -> None)
  | PatUC(fi1,p::ps,o1,u1),TmUC(fi2,UCLeaf([]),o2,u2) -> None
  | PatUC(fi1,p::ps,o1,u1),TmUC(fi2,UCNode(UCLeaf(t::ts),t2),o2,u2) ->
    (match eval_match env p t true with
    | Some(env,_) ->
      eval_match env (PatUC(fi1,ps,o1,u1))
        (TmUC(fi2,UCNode(UCLeaf(ts),t2),o2,u2)) final
    | None -> None)
  | PatUC(fi1,p::ps,o1,u1),TmUC(fi2,UCNode(UCLeaf([]),t2),o2,u2) ->
      eval_match env pat (TmUC(fi2,t2,o2,u2)) final
  | PatUC(fi1,[],o1,u1),TmUC(fi2,uct,_,_) when uctzero uct && final -> Some(env,TmNop)
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

    | Cnot,TmConst(fi,CBool(v)) -> TmConst(fi,CBool(not v))
    | Cnot,t -> fail_constapp (tm_info t)

    | Cand(None),TmConst(fi,CBool(v)) -> TmConst(fi,Cand(Some(v)))
    | Cand(Some(v1)),TmConst(fi,CBool(v2)) -> TmConst(fi,CBool(v1 && v2))
    | Cand(None),t | Cand(Some(_)),t  -> fail_constapp (tm_info t)

    | Cor(None),TmConst(fi,CBool(v)) -> TmConst(fi,Cor(Some(v)))
    | Cor(Some(v1)),TmConst(fi,CBool(v2)) -> TmConst(fi,CBool(v1 || v2))
    | Cor(None),t | Cor(Some(_)),t  -> fail_constapp (tm_info t)

    (* MCore integer intrinsics *)
    | CInt(_),t -> fail_constapp (tm_info t)

    | Caddi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Caddi(Some(v)))
    | Caddi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 + v2))
    | Caddi(None),t | Caddi(Some(_)),t  -> fail_constapp (tm_info t)

    | Csubi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Csubi(Some(v)))
    | Csubi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 - v2))
    | Csubi(None),t | Csubi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cmuli(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cmuli(Some(v)))
    | Cmuli(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 * v2))
    | Cmuli(None),t | Cmuli(Some(_)),t  -> fail_constapp (tm_info t)

    | Cdivi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cdivi(Some(v)))
    | Cdivi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 / v2))
    | Cdivi(None),t | Cdivi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cmodi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cmodi(Some(v)))
    | Cmodi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 mod v2))
    | Cmodi(None),t | Cmodi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cnegi,TmConst(fi,CInt(v)) -> TmConst(fi,CInt((-1)*v))
    | Cnegi,t -> fail_constapp (tm_info t)

    | Clti(None),TmConst(fi,CInt(v)) -> TmConst(fi,Clti(Some(v)))
    | Clti(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 < v2))
    | Clti(None),t | Clti(Some(_)),t  -> fail_constapp (tm_info t)

    | Cleqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cleqi(Some(v)))
    | Cleqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 <= v2))
    | Cleqi(None),t | Cleqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cgti(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cgti(Some(v)))
    | Cgti(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 > v2))
    | Cgti(None),t | Cgti(Some(_)),t  -> fail_constapp (tm_info t)

    | Cgeqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cgeqi(Some(v)))
    | Cgeqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 >= v2))
    | Cgeqi(None),t | Cgeqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Ceqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Ceqi(Some(v)))
    | Ceqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 = v2))
    | Ceqi(None),t | Ceqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cneqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cneqi(Some(v)))
    | Cneqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 <> v2))
    | Cneqi(None),t | Cneqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cslli(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cslli(Some(v)))
    | Cslli(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 lsl v2))
    | Cslli(None),t | Cslli(Some(_)),t  -> fail_constapp (tm_info t)

    | Csrli(None),TmConst(fi,CInt(v)) -> TmConst(fi,Csrli(Some(v)))
    | Csrli(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 lsr v2))
    | Csrli(None),t | Csrli(Some(_)),t  -> fail_constapp (tm_info t)

    | Csrai(None),TmConst(fi,CInt(v)) -> TmConst(fi,Csrai(Some(v)))
    | Csrai(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 asr v2))
    | Csrai(None),t | Csrai(Some(_)),t  -> fail_constapp (tm_info t)

    (* MCore intrinsic: Floating-point number constant and operations *)
    | CFloat(_),t -> fail_constapp (tm_info t)

    | Caddf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Caddf(Some(v)))
    | Caddf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 +. v2))
    | Caddf(None),t | Caddf(Some(_)),t  -> fail_constapp (tm_info t)

    | Csubf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Csubf(Some(v)))
    | Csubf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 -. v2))
    | Csubf(None),t | Csubf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cmulf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cmulf(Some(v)))
    | Cmulf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 *. v2))
    | Cmulf(None),t | Cmulf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cdivf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cdivf(Some(v)))
    | Cdivf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 /. v2))
    | Cdivf(None),t | Cdivf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cnegf,TmConst(fi,CFloat(v)) -> TmConst(fi,CFloat((-1.0)*.v))
    | Cnegf,t -> fail_constapp (tm_info t)

    (* Mcore intrinsic: Polymorphic integer and floating-point numbers *)

    | Cadd(TNone),TmConst(fi,CInt(v)) -> TmConst(fi,Cadd(TInt(v)))
    | Cadd(TNone),TmConst(fi,CFloat(v)) -> TmConst(fi,Cadd(TFloat(v)))
    | Cadd(TInt(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 + v2))
    | Cadd(TFloat(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 +. v2))
    | Cadd(TFloat(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CFloat(v1 +. (float_of_int v2)))
    | Cadd(TInt(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat((float_of_int v1) +. v2))
    | Cadd(_),t -> fail_constapp (tm_info t)

    | Csub(TNone),TmConst(fi,CInt(v)) -> TmConst(fi,Csub(TInt(v)))
    | Csub(TNone),TmConst(fi,CFloat(v)) -> TmConst(fi,Csub(TFloat(v)))
    | Csub(TInt(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 - v2))
    | Csub(TFloat(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 -. v2))
    | Csub(TFloat(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CFloat(v1 -. (float_of_int v2)))
    | Csub(TInt(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat((float_of_int v1) -. v2))
    | Csub(_),t -> fail_constapp (tm_info t)

    | Cmul(TNone),TmConst(fi,CInt(v)) -> TmConst(fi,Cmul(TInt(v)))
    | Cmul(TNone),TmConst(fi,CFloat(v)) -> TmConst(fi,Cmul(TFloat(v)))
    | Cmul(TInt(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 * v2))
    | Cmul(TFloat(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 *. v2))
    | Cmul(TFloat(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CFloat(v1 *. (float_of_int v2)))
    | Cmul(TInt(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat((float_of_int v1) *. v2))
    | Cmul(_),t -> fail_constapp (tm_info t)

    | Cdiv(TNone),TmConst(fi,CInt(v)) -> TmConst(fi,Cdiv(TInt(v)))
    | Cdiv(TNone),TmConst(fi,CFloat(v)) -> TmConst(fi,Cdiv(TFloat(v)))
    | Cdiv(TInt(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 / v2))
    | Cdiv(TFloat(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 /. v2))
    | Cdiv(TFloat(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CFloat(v1 /. (float_of_int v2)))
    | Cdiv(TInt(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat((float_of_int v1) /. v2))
    | Cdiv(_),t -> fail_constapp (tm_info t)

    | Cneg,TmConst(fi,CFloat(v)) -> TmConst(fi,CFloat((-1.0)*.v))
    | Cneg,TmConst(fi,CInt(v)) -> TmConst(fi,CInt((-1)*v))
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
      let lst = List.map (fun x -> ustring2uctm NoInfo (us x)) (!prog_argv)
      in TmUC(NoInfo,UCLeaf(lst),UCOrdered,UCMultivalued)
    | CConcat(None),t -> TmConst(NoInfo,CConcat((Some t)))
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
  | TmConst(_,Cmuli(Some(0))),v2 -> TmConst(fi,CInt(0))
  (*|   1 * x  ==>  x   |*)
  | TmConst(_,Cmuli(Some(1))),v2 -> v2
  (*|   0 + x  ==>  x   |*)
  | TmConst(_,Caddi(Some(0))),v2 -> v2
  (*|   0 * x  ==>  0   |*)
  | TmApp(_,TmConst(_,Cmuli(None)),TmConst(_,CInt(0))),vv1 -> TmConst(fi,CInt(0))
  (*|   1 * x  ==>  x   |*)
  | TmApp(_,TmConst(_,Cmuli(None)),TmConst(_,CInt(1))),vv1 -> vv1
  (*|   0 + x  ==>  x   |*)
  | TmApp(_,TmConst(_,Caddi(None)),TmConst(_,CInt(0))),vv1 -> vv1
  (*|   x * 0  ==>  0   |*)
  | TmApp(_,TmConst(_,Cmuli(None)),vv1),TmConst(_,CInt(0)) -> TmConst(fi,CInt(0))
  (*|   x * 1  ==>  x   |*)
  | TmApp(_,TmConst(_,Cmuli(None)),vv1),TmConst(_,CInt(1)) -> vv1
  (*|   x + 0  ==>  x   |*)
  | TmApp(_,TmConst(_,Caddi(None)),vv1),TmConst(_,CInt(0)) -> vv1
  (*|   x - 0  ==>  x   |*)
  | TmApp(_,TmConst(_,Csubi(None)),vv1),TmConst(_,CInt(0)) -> vv1
  (*|   x op y  ==>  res(x op y)   |*)
  | TmConst(fi1,c1),(TmConst(fi2,c2) as tt)-> delta c1 tt
  (* No optimization *)
  | vv1,vv2 -> TmApp(fi,vv1,vv2)

(*eval helper methods*)
let rec add_evaluated_term_to_args args term =
  match args with
  | [] -> term::[]
  | hd::tl -> hd::(add_evaluated_term_to_args tl term)

let get_arg_types_length_dummy fi fun_name =
  match Ustring.to_utf8 fun_name with
  | "length" -> 0
  | "nth" -> 1
  | "push" -> 1
  | _ -> raise_error fi "Sequence method not implemented."

let get_last_arg_index fun_name =
  (*TODO: Check length of arg types in sequence function table*)
  get_arg_types_length_dummy fun_name

let call_seq_method fi ds_choice fun_name args =
  (*TODO: Open ds_choice for method*)
  (*TODO: Check arg types against sequence function table*)
  (*TODO: Check that number of arguments are correct (earlier?)*)
  match Ustring.to_utf8 fun_name with
  | "length" ->
    (match (List.nth args 0) with
    | TmSeq(fi2,ty_2,ds_choice2,clist,cseq) ->
      let seq_length = List.length (Ast.get_list_from_clist clist) in
      TmConst(fi, CInt(seq_length))
    | _ -> raise_error fi "Argument has the wrong type.")
  | "nth" ->
    (match (List.nth args 0), (List.nth args 1) with
     | TmSeq(fi2,ty_2,ds_choice2,clist,cseq), TmConst(fi3,CInt(n)) ->
       let nth_element = List.nth (Ast.get_list_from_clist clist) n in
       TmConst(fi, CInt(nth_element))
     | _ -> raise_error fi "Arguments have the wrong type.")
  | "push" ->
    (match (List.nth args 0), (List.nth args 1) with
     | TmSeq(fi2,ty_2,ds_choice2,clist,cseq), TmConst(fi3, CInt(e)) ->
       let updated_clist = CIntList(e::(Ast.get_list_from_clist clist)) in
       TmSeq(fi2,ty_2,ds_choice2,updated_clist,cseq)
     | _ -> raise_error fi "Argument has the wrong type.")
  | _ -> raise_error fi "Sequence method not implemented."

(* Main evaluation loop of a term. Evaluates using big-step semantics *)
let rec eval env t =
  debug_eval env t;
  match t with
  (* Variables using debruijn indices. Need to evaluate because fix point. *)
  | TmVar(fi,x,n,_) -> eval env  (List.nth env n)
  (* Lambda and closure conversions *)
  | TmLam(fi,x,ty,t1) -> TmClos(fi,x,ty,t1,env,false)
  | TmClos(fi,x,_,t1,env2,_) -> t
  (* Application *)
  | TmApp(fi,t1,t2) ->
      (match eval env t1 with
       (* Closure application *)
       | TmClos(fi,x,_,t3,env2,_) -> eval ((eval env t2)::env2) t3
       (* Constant application using the delta function *)
       | TmConst(fi,c) -> delta c (eval env t2)
       (* Fix *)
       | TmFix(fi) ->
         (match eval env t2 with
         | TmClos(fi,x,_,t3,env2,_) as tt -> eval ((TmApp(fi,TmFix(fi),tt))::env2) t3
         | _ -> failwith "Incorrect CFix")
       | TmSeqMethod(fi,ds_choice,fun_name,args,arg_index) ->
         let updated_args = add_evaluated_term_to_args args (eval env t2) in
         let last_arg_index = get_last_arg_index fi fun_name in
         if arg_index == last_arg_index then
           call_seq_method fi ds_choice fun_name updated_args
         else if arg_index < last_arg_index then
           TmSeqMethod(fi,ds_choice,fun_name,updated_args,(arg_index+1))
         else
           raise_error fi "Argument index is out of bounds."
       | _ -> raise_error fi "Application to a non closure value.")
  (* Constant *)
  | TmConst(_,_) | TmFix(_) -> t
  (* System F terms *)
  | TmTyLam(fi,_,_,_) | TmTyApp(fi,_,_) -> failwith "System F terms should not exist (4)"
  (* If expression *)
  | TmIfexp(fi,cnd,thn,els) ->
    (match eval env cnd with
     | TmConst(_,CBool(b)) ->
       if b then
         eval env thn
       else
         eval env els
     | _ -> raise_error fi "Condition in if-expression not a bool.")
  (* Sequence constructor *)
  | TmSeq(_,_,_,_,_) -> t
  (* Sequence method*)
  | TmSeqMethod(_,_,_,_,_) -> t
  (* The rest *)
  | TmChar(_,_) -> t
  | TmUC(fi,uct,o,u) -> TmUC(fi,ucmap (eval env) uct,o,u)
  | TmUtest(fi,t1,t2,tnext) ->
    if !utest then begin
      let (v1,v2) = ((eval env t1),(eval env t2)) in
        if val_equal v1 v2 then
         (printf "."; utest_ok := !utest_ok + 1)
       else (
        unittest_failed fi v1 v2;
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
     end;
    eval env tnext
  | TmMatch(fi,t1,cases) -> (
     let v1 = make_tm_for_match (eval env t1) in
     let rec appcases cases =
       match cases with
       | Case(_,p,t)::cs ->
          (match eval_match env p v1 true with
         | Some(env,_) -> eval env t
         | None -> appcases cs)
       | [] -> raise_error fi  "Match error"
     in
      appcases cases)
  | TmNop -> t


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
        |> eval (builtin |> List.split |> snd |> List.map (fun x -> TmConst(NoInfo,x)))
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
