

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
open Errors

(* Debug options *)
let enable_debug_type_checking = false


(* Generic type checking function *)
let tydebug desc strlst tmlst tylst =
  if not enable_debug_type_checking then () else (
  printf "------------ %s START ------- \n" desc;
  List.iter (fun (x,xs) -> uprint_endline (us x ^. us": " ^. xs)) strlst;
  List.iter (fun (x,t) -> uprint_endline (us x ^. us": " ^. (pprint true t))) tmlst;
  List.iter (fun (x,ty) -> uprint_endline (us x ^. us": " ^. (pprint_ty ty))) tylst;
  printf "------------- %s END -------- \n" desc)

(* Perform index shifting, as part of the capture free type substitution *)
let rec tyShift d c ty =
  match ty with
  | TyGround(fi,gt) -> ty
  | TyArrow(fi,ty1,ty2) -> TyArrow(fi,tyShift d c ty1, tyShift d c ty2)
  | TyVar(fi,x,k) -> TyVar(fi,x,if k < c then k else k + d)
  | TyAll(fi,x,kind,ty2) -> TyAll(fi,x,kind, tyShift d (c+1) ty2)
  | TyLam(fi,x,kind,ty1) -> TyLam(fi,x,kind, tyShift d (c+1) ty1)
  | TyApp(fi,ty1,ty2) -> TyApp(fi, tyShift d c ty1, tyShift d c ty2)
  | TyDyn -> TyDyn
  | TySeq(seq_ty) -> TySeq(tyShift d c seq_ty)


(* Substitutes type [tys] in ty *)
let tySubst tys ty =
  let rec subst j s ty =
    (match ty with
    | TyGround(fi,gt) -> ty
    | TyArrow(fi,ty1,ty2) -> TyArrow(fi, subst j s ty1, subst j s ty2)
    | TyVar(fi,x,k) -> if k = j then s else TyVar(fi,x,k)
    | TyAll(fi,x,kind,ty2) -> TyAll(fi,x,kind, subst (j+1) (tyShift 1 0 s) ty2)
    | TyLam(fi,x,kind,ty1) -> TyLam(fi,x,kind, subst (j+1) (tyShift 1 0 s) ty1)
    | TyApp(fi,ty1,ty2) -> TyApp(fi, subst j s ty1, subst j s ty2)
    | TyDyn -> TyDyn
    | TySeq(seq_ty) -> TySeq((subst j s seq_ty)))
  in
    subst 0 tys ty


let tySubstTop tys ty =
  tyShift (-1) 0 (tySubst (tyShift 1 0 tys) ty)

(* Checks if two kinds are equal *)
let rec kindEqual ki1 ki2 =
  match ki1,ki2 with
  | KindStar(_),KindStar(_) -> true
  | KindArrow(_,ki11,ki12),KindArrow(_,ki21,ki22) ->
      (kindEqual ki11 ki21) && (kindEqual ki12 ki22)
  | KindArrow(_,_,_),_ | _,KindArrow(_,_,_) -> false


(* Parallel reduction. Reduce types into normal form.
   Used for checking type equivalence *)
let normTy ty =
  let rec reduce ty =
    match ty with
    | TyGround(fi,gt) -> ty
    | TyArrow(fi,ty1,ty2) -> TyArrow(fi,reduce ty1,reduce ty2)
    | TyVar(fi,x,n) -> TyVar(fi,x,n)
    | TyAll(fi,x,ki1,ty1) -> TyAll(fi,x,ki1,reduce ty1)
    | TyLam(fi,x,ki1,ty1) -> TyLam(fi,x,ki1,reduce ty1)
    | TyApp(fi,ty1,ty2) ->
      (match reduce ty1, reduce ty2 with
       | TyLam(fi3,x,ki3,ty3),ty4 -> reduce (tySubstTop ty4 ty3)
       | ty1',ty2' -> TyApp(fi,ty1',ty2'))
    | TyDyn -> TyDyn
    | TySeq(seq_ty) -> TySeq(seq_ty)
  in
    reduce ty


(* Checks if two types are equal *)
let tyequal ty1 ty2 =
  let rec tyrec ty1 ty2 =
    match ty1,ty2 with
    | TyGround(_,g1),TyGround(_,g2) -> g1 = g2
    | TyArrow(_,ty11,ty12),TyArrow(_,ty21,ty22) ->
      tyrec ty11 ty21 &&  tyrec ty21 ty22
    | TyVar(_,_,n1),TyVar(_,_,n2) -> n1 = n2
    | TyAll(_,x1,_,ty1),TyAll(_,x2,_,ty2) -> tyrec ty1 ty2
    | TyLam(fi1,x1,kind1,ty1), TyLam(fi2,x2,kind2,ty2) ->
      tyrec ty1 ty2 && kindEqual kind1 kind2
    | TyApp(fi1,ty11,ty12), TyApp(fi2,ty21,ty22)->
      tyrec ty11 ty21 && tyrec ty12 ty22
    | TyDyn,TyDyn -> true
    | TySeq(seq_ty1),TySeq(seq_ty2) ->
      tyrec seq_ty1 seq_ty2
    | TyGround(_,_), _ | _,TyGround(_,_) -> false
    | TyArrow(_,_,_), _ | _,TyArrow(_,_,_) -> false
    | TyVar(_,_,_), _ | _,TyVar(_,_,_) -> false
    | TyAll(_,_,_,_), _ | _,TyAll(_,_,_,_) -> false
    | TyLam(fi,x,kind,ty1),_ | _,TyLam(fi,x,kind,ty1) -> false
    | TyApp(fi,ty1,ty2),_ | _,TyApp(fi,ty1,ty2)-> false
    | TySeq(seq_ty),_ | _,TySeq(seq_ty) -> false
  in
    tyrec ty1 ty2


(* TODO: Should constants carry their types? *)
(* Returns the type of a constant value *)
let type_const c =
  let tyarr t1 t2 = TyArrow(NoInfo,t1,t2) in
  let tybool = TyGround(NoInfo,GBool) in
  let tyint =  TyGround(NoInfo,GInt) in
  let tyfloat =  TyGround(NoInfo,GFloat) in
  match c with
  (* MCore intrinsic: Boolean constant and operations *)
  | CBool(_) -> tybool
  | Cnot -> tyarr tybool tybool
  | Cand(None) | Cor(None) -> tyarr tybool (tyarr tybool tybool)
  | Cand(_) | Cor(_) -> tyarr tybool tybool
(* MCore intrinsic: Integer constant and operations *)
  | CInt(_) -> tyint
  | Caddi(None) | Csubi(None) | Cmuli(None)| Cdivi(None) | Cmodi(None)
      -> tyarr tyint (tyarr tyint tyint)
  | Caddi(_) | Csubi(_) | Cmuli(_)| Cdivi(_) | Cmodi(_) | Cnegi
      -> tyarr tyint tyint
  | Clti(None) | Cleqi(None) | Cgti(None)  | Cgeqi(None) | Ceqi(None)
               | Cneqi(None) | Cslli(None) | Csrli(None) | Csrai(None)
      -> tyarr tyint (tyarr tyint tybool)
  | Clti(_) | Cleqi(_) | Cgti(_)  | Cgeqi(_) | Ceqi(_)
            | Cneqi(_) | Cslli(_) | Csrli(_) | Csrai(_)
      -> tyarr tyint tybool
(* MCore intrinsic: Floating-point number constant and operations *)
  | CFloat(_) -> tyfloat
  | Caddf(None) | Csubf(None) | Cmulf(None) | Cdivf(None)
      -> tyarr tyfloat (tyarr tyfloat tyfloat)
  | Caddf(_) | Csubf(_) | Cmulf(_) | Cdivf(_) | Cnegf
      -> tyarr tyfloat tyfloat
(* Mcore intrinsic: Polymorphic integer and floating-point numbers *)
  | Cadd(_) | Csub(_) | Cmul(_) | Cdiv(_) | Cneg
(* MCore debug and I/O intrinsics *)
  | CDStr | CDPrint | CPrint | CArgv
(* MCore unified collection type (UCT) intrinsics *)
  | CConcat(_)
(* Atom - an untyped lable that can be used to implement domain specific constructs *)
  | CAtom(_,_)
    -> error NoInfo (us"The constant is not supported in the current type system")




(* Returns the kind of a specific type *)
let rec kindof env ty =
  match ty with
  | TyGround(fi,gt) -> KindStar(fi)
  | TyArrow(fi,ty1,ty2) ->
    let kcheck ki fi  =
      match ki with
      | KindStar(_) -> ()
      | _ -> error fi (us"Type has kind " ^.
             pprint_kind ki ^. us", but kind * was expected")
    in kcheck (kindof env ty1) (ty_info ty1);
       kcheck (kindof env ty2) (ty_info ty2);
       KindStar(fi)
  | TyVar(fi,x,n) ->
      (match List.nth_opt env n with
       | Some(TyenvTyvar(y,ki1)) -> ki1
       | _ -> error fi (us"Variable '" ^. x ^. us"' cannot be found."))
  | TyAll(fi,x,ki1,ty1) ->
      (match kindof (TyenvTyvar(x,ki1)::env) ty1 with
       | KindStar(_) as ki2 -> ki2
       | ki3 -> error fi (us"The type is of kind " ^. pprint_kind ki3 ^.
                          us", but kind * was expected"))
  | TyLam(fi,x,ki1,ty1) ->
      let ki2 =  kindof (TyenvTyvar(x,ki1)::env) ty1 in
      KindArrow(fi,ki1,ki2)
  | TyApp(fi,ty1,ty2) ->
      (match kindof env ty1, kindof env ty2 with
       | KindArrow(fi2,k11,k12),k11' ->
         if kindEqual k11 k11' then k12
         else error (ty_info ty2) (us"Incorrect type-level application. " ^.
           us"The type argument is of kind " ^. pprint_kind k11' ^.
           us", but kind " ^. pprint_kind k11 ^. us" was expected.")
       | k1,_ -> error (ty_info ty1) (us"Incorrect type-level application. " ^.
           us"Kind " ^. pprint_kind k1 ^.us" is not a kind of a type-level function"))
  | TyDyn -> KindStar(NoInfo)
  | TySeq(_) -> KindStar(NoInfo)


(* Returns true of the type contains at least one TyDyn *)
let rec containsTyDyn ty =
  match ty with
  | TyGround(fi,gt) -> false
  | TyArrow(fi,ty1,ty2) -> containsTyDyn ty1 || containsTyDyn ty2
  | TyVar(fi,x,n) -> false
  | TyAll(fi,x,ki1,ty1) -> containsTyDyn ty1
  | TyLam(fi,x,ki1,ty1) -> containsTyDyn ty1
  | TyApp(fi,ty1,ty2) -> containsTyDyn ty1 || containsTyDyn ty2
  | TyDyn -> true
  | TySeq(seq_ty) -> containsTyDyn seq_ty


(* Returns true of the type contains at least one TyVar *)
let containsFreeTyVar ty =
  let rec work c ty =
  match ty with
  | TyGround(fi,gt) -> false
  | TyArrow(fi,ty1,ty2) -> work c ty1 || work c ty2
  | TyVar(fi,x,n) -> (n >= c)
  | TyAll(fi,x,ki1,ty1) -> work (c+1) ty1
  | TyLam(fi,x,ki1,ty1) -> work (c+1) ty1
  | TyApp(fi,ty1,ty2) -> work c ty1 || work c ty2
  | TyDyn -> false
  | TySeq(seq_ty) -> work c seq_ty
  in work 0 ty


(* Check if there is a free variable with index 0 *)
let isTyVarFree ty =
  let rec work d ty =
  match ty with
  | TyGround(fi,gt) -> false
  | TyArrow(fi,ty1,ty2) -> work d ty1 || work d ty2
  | TyVar(fi,x,n) -> (n = d)
  | TyAll(fi,x,ki1,ty1) -> work (d+1) ty1
  | TyLam(fi,x,ki1,ty1) -> work (d+1) ty1
  | TyApp(fi,ty1,ty2) -> work d ty1 || work d ty2
  | TyDyn -> false
  | TySeq(seq_ty) -> work d seq_ty
  in work 0 ty


let rec substAll env ty =
  match ty with
  | TyGround(fi,gt) -> ty
  | TyArrow(fi,ty1,ty2) -> TyArrow(fi, substAll env ty1, substAll env ty2)
  | TyVar(fi,x,k) ->
    (match List.nth_opt env k with
    | Some(Some(ty2)) -> ty2
    | Some(None) -> ty
    | _ -> ty)
  | TyAll(fi,x,kind,ty2) -> TyAll(fi,x,kind, substAll (None::env) ty2)
  | TyLam(fi,x,kind,ty1) -> TyLam(fi,x,kind, substAll (None::env) ty1)
  | TyApp(fi,ty1,ty2) -> TyApp(fi, substAll env ty1, substAll env ty2)
  | TyDyn -> TyDyn
  | TySeq(seq_ty) -> TySeq(substAll env seq_ty)



(* Merge two types. Assumes that the input types are normalized.
   The merge environment [env] is a list of options, where None means that
   the variable cannot be bound becase it is a local 'all' binder, whereas Some(ty)
   is the type that the variable is bounded to.
   Returns None if they do not match and Some(ty',senv), where ty' is the merged new
   type and senv is the variable substitution environment. *)
let tyMerge ty1 ty2 =
  let rec updateEnv env n ty =
    (match env with
    | None::_ when n = 0 -> raise Not_found
    | Some(_)::xs when n = 0 -> Some(ty)::xs
    | x::xs -> x::(updateEnv xs (n-1) ty)
    | [] -> updateEnv [Some(TyDyn)] n ty)
  in
  let rec tyRec ty1 ty2 env =
    (match ty1,ty2 with
     | TyGround(_,g1),TyGround(_,g2) -> if g1 = g2 then (ty1,env) else raise Not_found
     | (TyGround(_,_) as ty), TyDyn | TyDyn,(TyGround(_,_) as ty) -> (ty,env)
     | TyArrow(fi,ty11,ty12),TyArrow(_,ty21,ty22) ->
       let (ty1',env1) = tyRec ty11 ty21 env in
       let (ty2',env2) = tyRec ty12 ty22 env1 in
         (TyArrow(fi,ty1',ty2'),env2)
     | TyArrow(fi,ty1,ty2),TyDyn | TyDyn,TyArrow(fi,ty1,ty2) ->
         (TyArrow(fi,ty1,ty2),env)
     | TyVar(fi,x,n1),TyVar(_,_,n2) ->
       if n1 = n2 then (ty1,env) else raise Not_found
     | TyVar(fi,x,n),TyDyn | TyDyn,TyVar(fi,x,n) -> (TyVar(fi,x,n),env)
     | TyVar(fi,x,n),ty2 | ty2,TyVar(fi,x,n) ->
         if containsFreeTyVar ty2 then raise Not_found else
         (ty2, (updateEnv env n ty2))
     | TyAll(fi1,x,ki1,ty1),TyAll(fi2,_,ki2,ty2) ->
         if not (kindEqual ki1 ki2) then raise Not_found else
           let (ty',env2) = tyRec ty1 ty2 (None::env) in
           (TyAll(fi1,x,ki1,ty'),env)
     | TyAll(fi1,x,ki1,ty1),TyDyn | TyDyn,TyAll(fi1,x,ki1,ty1) ->
         (TyAll(fi1,x,ki1,ty1), env)
     | TyLam(fi1,x1,kind1,ty1), TyLam(fi2,x2,kind2,ty2) -> failwith "TODO TyLam"
     | TyApp(fi1,ty11,ty12), TyApp(fi2,ty21,ty22)-> failwith "TODO TyApp"
     | TyDyn,TyDyn -> (TyDyn,env)
     | TyArrow(_,_,_), _ | _,TyArrow(_,_,_) -> raise Not_found
     | TyAll(_,_,_,_), _ | _,TyAll(_,_,_,_) -> raise Not_found
     | TyLam(fi,x,kind,ty1),_ | _,TyLam(fi,x,kind,ty1) -> failwith "TODO TyLam"
     | TyApp(fi,ty1,ty2),_ | _,TyApp(fi,ty1,ty2)-> failwith "TODO TyApp"
     | TySeq(seq_ty1),TySeq(seq_ty2) -> (TySeq(seq_ty1),env) (*TODO*)
     | TySeq(seq_ty),TyDyn -> (TySeq(seq_ty),env)
     | TyDyn,TySeq(seq_ty) -> (TySeq(seq_ty),env)
     | TySeq(seq_ty),TyGround(_,_) -> tyRec seq_ty ty2 env
     | TyGround(_,_),TySeq(seq_ty) -> tyRec seq_ty ty1 env
    )
  in
  try Some(tyRec ty1 ty2 [])
  with _ -> None


let setType ty = function
  | TmVar(ti,x,n,pe) -> TmVar({ti with ety = Some ty},x,n,pe)
  | TmLam(ti,x,ty1,t1) -> TmLam({ti with ety = Some ty},x,ty1,t1)
  | TmClos(ti,s,ty,t1,env1,pe) -> TmClos({ti with ety = Some ty},s,ty,t1,env1,pe)
  | TmApp(ti,t1,t2) -> TmApp({ti with ety = Some ty},t1,t2)
  | TmConst(ti,c) -> TmConst({ti with ety = Some ty},c)
  | TmIfexp(ti,cnd,thn,els) -> TmIfexp({ti with ety = Some ty},cnd,thn,els)
  | TmFix(ti) -> TmFix({ti with ety = Some ty})
  | TmTyLam(ti,x,kind,t1) -> TmTyLam({ti with ety = Some ty},x,kind,t1)
  | TmTyApp(ti,t1,ty2) -> TmTyApp({ti with ety = Some ty},t1,ty2)
  | TmSeq(ti,ty_ident,tmlist,tmseq,ds_choice) -> TmSeq({ti with ety = Some ty},ty_ident,tmlist,tmseq,ds_choice)
  | TmSeqMethod(ti,fun_name,actual_fun,args,arg_index,ds_choice,in_fix) ->
    TmSeqMethod({ti with ety = Some ty},fun_name,actual_fun,args,arg_index,ds_choice,in_fix)
  | TmChar(ti,x) -> TmChar({ti with ety = Some ty},x)
  | TmUC(ti,tree,ord,unique) -> TmUC({ti with ety = Some ty},tree,ord,unique)
  | TmUtest(ti,t1,t2,t3) -> TmUtest({ti with ety = Some ty},t1,t2,t3)
  | TmMatch(ti,t1,cases) -> TmMatch({ti with ety = Some ty},t1,cases)
  | TmNop -> TmNop

let getType t =
  let extract = function
    | Some ty -> ty
    | None -> failwith ("Term does not have a set type: "^Ustring.to_utf8 (pprint true t))
  in
  match t with
  | TmVar({ety},_,_,_) -> extract ety
  | TmLam({ety},_,_,_) -> extract ety
  | TmClos({ety},_,_,_,_,_) -> extract ety
  | TmApp({ety},_,_) -> extract ety
  | TmConst({ety},_) -> extract ety
  | TmIfexp({ety},_,_,_) -> extract ety
  | TmFix({ety}) -> extract ety
  | TmTyLam({ety},_,_,_) -> extract ety
  | TmTyApp({ety},_,_) -> extract ety
  | TmSeq({ety},_,_,_,_) -> extract ety
  | TmSeqMethod({ety},_,_,_,_,_,_) -> extract ety

  | TmChar({ety},_) -> extract ety
  | TmUC({ety},_,_,_) -> extract ety
  | TmUtest({ety},_,_,_) -> extract ety
  | TmMatch({ety},_,_) -> extract ety
  | TmNop -> TyGround(NoInfo,GVoid)

let get_seq_fun_type fun_name fi =
  match Ustring.to_utf8 fun_name with
  | "is_empty" ->
    TyAll(fi,us"a",KindStar(fi),TyArrow(fi,TySeq(TyVar(fi,us"a",0)),TyGround(NoInfo,GBool)))
  | "first" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TySeq(TyVar(fi,us"a",0)),
                  TyVar(fi,us"a",0)))
  | "last" ->
    TyAll(fi,us"a",KindStar(fi),TyArrow(fi,TySeq(TyVar(fi,us"a",0)),TyVar(fi,us"a",0)))
  | "push" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TySeq(TyVar(fi,us"a",0)),
                  TyArrow(fi,
                          TyVar(fi,us"a",0),
                          TySeq(TyVar(fi,us"a",0)))))
  | "pop" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TySeq(TyVar(fi,us"a",0)),
                  TySeq(TyVar(fi,us"a",0))))
  | "length" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TySeq(TyVar(fi,us"a",0)),
                  TyGround(fi,GInt)))
  | "nth" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TySeq(TyVar(fi,us"a",0)),
                  TyArrow(fi,
                          TyGround(fi,GInt),
                          TyVar(fi,us"a",0))))
  | "append" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TySeq(TyVar(fi,us"a",0)),
                  TyArrow(fi,
                          TySeq(TyVar(fi,us"a",0)),
                          TySeq(TyVar(fi,us"a",0)))))
  | "reverse" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TySeq(TyVar(fi,us"a",0)),
                  TySeq(TyVar(fi,us"a",0))))
  | "push_last" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TySeq(TyVar(fi,us"a",0)),
                  TyArrow(fi,
                          TyVar(fi,us"a",0),
                          TySeq(TyVar(fi,us"a",0)))))
  | "pop_last" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TySeq(TyVar(fi,us"a",0)),
                  TySeq(TyVar(fi,us"a",0))))
  | "take" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TySeq(TyVar(fi,us"a",0)),
                  TyArrow(fi,
                          TyGround(fi,GInt),
                          TySeq(TyVar(fi,us"a",0)))))
  | "drop" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TySeq(TyVar(fi,us"a",0)),
                  TyArrow(fi,
                          TyGround(fi,GInt),
                          TySeq(TyVar(fi,us"a",0)))))
  | "map" ->
    TyAll(fi,us"a",KindStar(fi),
          TyAll(fi,us"b",KindStar(fi),
                TyArrow(fi,
                        TyArrow(fi,
                                TyVar(fi,us"a",0),
                                TyVar(fi,us"b",0)),
                        TyArrow(fi,
                                TySeq(TyVar(fi,us"a",0)),
                                TySeq(TyVar(fi,us"b",0))))))
  | "any" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TyArrow(fi,
                          TyVar(fi,us"a",0),
                          TyGround(fi,GBool)),
                  TyArrow(fi,
                          TySeq(TyVar(fi,us"a",0)),
                          TyGround(fi,GBool))))
  | "seqall" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TyArrow(fi,
                          TyVar(fi,us"a",0),
                          TyGround(fi,GBool)),
                  TyArrow(fi,
                          TySeq(TyVar(fi,us"a",0)),
                          TyGround(fi,GBool))))
  | "find" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TyArrow(fi,
                          TyVar(fi,us"a",0),
                          TyGround(fi,GBool)),
                  TyArrow(fi,
                          TySeq(TyVar(fi,us"a",0)),
                          TyVar(fi,us"a",0))))
  | "filter" ->
    TyAll(fi,us"a",KindStar(fi),
          TyArrow(fi,
                  TyArrow(fi,
                          TyVar(fi,us"a",0),
                          TyGround(fi,GBool)),
                  TyArrow(fi,
                          TySeq(TyVar(fi,us"a",0)),
                          TySeq(TyVar(fi,us"a",0)))))
  | "foldr" ->
    TyAll(fi,us"a",KindStar(fi),
          TyAll(fi,us"b",KindStar(fi),
                TyArrow(fi,
                        TyArrow(fi,
                                TyVar(fi,us"a",0),
                                TyArrow(fi,
                                        TyVar(fi,us"b",0),
                                        TyVar(fi,us"b",0))),
                        TyArrow(fi,
                                TyVar(fi,us"b",0),
                                TyArrow(fi,
                                        TySeq(TyVar(fi,us"a",0)),
                                        TyVar(fi,us"b",0))))))
  | "foldl" ->
    TyAll(fi,us"b",KindStar(fi),
          TyAll(fi,us"a",KindStar(fi),
                TyArrow(fi,
                        TyArrow(fi,
                                TyVar(fi,us"b",0),
                                TyArrow(fi,
                                        TyVar(fi,us"a",0),
                                        TyVar(fi,us"b",0))),
                        TyArrow(fi,
                                TyVar(fi,us"b",0),
                                TyArrow(fi,
                                        TySeq(TyVar(fi,us"a",0)),
                                        TyVar(fi,us"b",0))))))
  | _ -> failwith "We don't have type of this function"

let rec check_types_of_list tm_l seq_ty =
  match tm_l with
  | [] -> true
  | hd::tl ->
    if tyequal (getType hd) seq_ty then
      let res = check_types_of_list tl seq_ty in
      res
    else
      failwith "One of the elements in the list has the wrong type" (*TODO: raise instead?*)

let get_element_ty fi ty_ident =
  match (Ustring.to_utf8 ty_ident) with
  | "int" -> TyGround(NoInfo,GInt)
  | _ -> failwith "Element type not allowed yet"

let rec get_tyarrow_return_type ty =
  match ty with
  | TyArrow(_,_,retty) ->
    get_tyarrow_return_type retty
  | _ -> ty

(* Bidirectional type checking where type variable application is not needed.
   Main idea: propagate both types and type environment (filled will
     bindings of type vars) in both directions, merging partially filled in
     types. The 'holes' in the types are marked using type TyDyn. If
     type reconstruction is complete, the TyDyn does not exist anywhere.
   Future: we can combine let-polymorphism, gradual typing, and this
     reconstruction of for type applications in system F using bidirectional
     type checking. Should in such case mark code as gradually typed, that
     allows TyDyn to be left, but still generates System F code. *)
let rec tc env ty t =
  let rec tc_list tm_l = (
    match tm_l with
    | [] -> []
    | hd::tl -> (tc env TyDyn hd)::(tc_list tl)
  ) in
  match t with
  | TmVar(ti,x,n,pe) ->
    (match List.nth_opt env n with
    | Some(TyenvTmvar(y,ty1)) ->
      let tys = tyShift (n+1) 0 ty1 in
      tydebug "TmVar" [("n",us(sprintf "%d" n));("x",x)] [] [("tys",tys)];
      setType tys t
    | _ -> errorVarNotFound ti.fi x)
  | TmLam(ti,x,ty1,t1) ->
    let (ty1in,ty2in) =
      (match ty with TyArrow(_,ty1,ty2) -> (ty1,ty2)| _ -> (TyDyn,TyDyn))
    in
     tydebug "TmLam" [] [("t",t)] [("ty1in",ty1in);("ty1",ty1);("ty2in",ty2in)];
     (match tyMerge ty1 ty1in with
      | None ->
        errorInferredTypeMismatch ti.fi ty1 ty1in
      | Some(ty1b,substEnv) ->
       let ty1b = substAll substEnv ty1b in
       let t1' = tc (TyenvTmvar(x,ty1b)::env) ty2in t1 in
       let ty2b = getType t1' in
       let ty2shift = tyShift (-1) 0 ty2b in
       setType (TyArrow(ti.fi,ty1b,ty2shift)) (TmLam(ti,x,ty1,t1')))
  | TmClos(ti,s,ty,t1,env1,pe) -> errorImpossible ti.fi
  | TmApp(ti,t1,t2) ->
    let t2' = tc env TyDyn t2 in
    let ty2' =
     (match t2' with
     | TmLam(_,_,TyDyn,_) -> TyDyn
     | _ -> getType t2') in
    let t1' = tc env (TyArrow(ti.fi,ty2',ty)) t1 in
    let ty1' = getType t1' in
    tydebug "TmApp" [] [("t1",t1)] [("ty1'",ty1');("ty2'",ty2')];
    if containsTyDyn ty1' then errorCannotInferType (tm_info t1) ty1'
    else
      let rec dive ty1' ty2' env s =
        (match ty1' with
         | TyArrow(fi3,ty11,ty12) ->
           (* TODO Elias: The then-case might not be right... *)
           let ty22 = if containsTyDyn ty2' then
               getType (tc env ty11 t2)
             else
               ty2' in
           if containsTyDyn ty22 then errorCannotInferType (tm_info t2) ty22 else
             let ty22s = tyShift s 0 ty22 in
             (match tyMerge ty11 ty22s with
             | None -> errorFuncAppMismatch (tm_info t2) ty11 ty22s
             | Some(ty11',substEnv) ->
               let res = substAll substEnv ty12 in
               let res2 =
                 (match t1' with
                  | TmFix _ ->
                    (match ty1' with
                     | TyArrow(_,arrty1,arrty2) ->
                       (match arrty1 with
                        | TyArrow(_,arrty1',arrty2') ->
                          arrty1'
                        | _ -> res)
                     | _ -> res
                    )
                  | _ -> res
                 ) in
             res2)
        | TyAll(fi,x,ki,ty4) ->
          let ty' = dive ty4 ty2' env (s+1) in
          if isTyVarFree ty' then
            TyAll(fi,x,ki,ty')
          else
            ty'
        | _ ->
          errorNotFunctionType (tm_info t1) ty1')
      in
      let resTy = dive ty1' ty2' env 0 in
      setType resTy (TmApp(ti, t1', t2'))
  | TmConst(ti,c) -> setType (type_const c) t
  | TmIfexp(ti,cnd,thn,els) ->
    let updated_cnd = tc env TyDyn cnd in
    let updated_thn = tc env TyDyn thn in
    let updated_els = tc env TyDyn els in
    let _ = (match getType updated_cnd with
    | TyGround(_,GBool) -> true
    | _ -> failwith "Condition has to be of type boolean") in
    let _ = (match tyequal (getType updated_thn) (getType updated_els) with
    | true -> true
    | _ -> failwith "Then and else has to be of the same type") in
    setType (getType updated_thn) (TmIfexp(ti,updated_cnd,updated_thn,updated_els))
  | TmFix(ti) ->
    (match ty with
     | TyArrow(_,arrty1,TyDyn) ->
       let retty = get_tyarrow_return_type arrty1 in
       setType (TyArrow(NoInfo,arrty1,retty)) t
     | _ ->
       setType ty t)
  | TmTyLam(ti,x,kind,t1) ->
    let t1' = tc (TyenvTyvar(x,kind)::env) TyDyn t1 in
    let ty1' = getType t1' in
    tydebug "TmTyLam" [("x",x)] [] [("ty1'",ty1')];
    setType (TyAll(ti.fi,x,kind,ty1')) (TmTyLam(ti,x,kind,t1'))
  | TmTyApp(ti,t1,ty2) ->
    let t1' = tc env TyDyn t1 in
    let ty1' = getType t1' in
    (match ty1' with
     | TyAll(fi2,x,ki11,ty1) ->
       let ki12 = kindof env ty2 in
       let resTy = if kindEqual ki11 ki12 then tySubstTop ty2 ty1
         else errorKindMismatch  (ty_info ty2) ki11 ki12 in
       setType resTy (TmTyApp(ti,t1',ty2))
     | ty -> errorExpectsUniversal (tm_info t1) ty)
  | TmSeq(ti,ty_ident,tmlist,tmseq,ds_choice) ->
    let updated_tmlist = tc_list (Ast.get_list_from_tmlist tmlist) in
    let e_ty = get_element_ty (tm_info t) ty_ident in
    let _ = check_types_of_list updated_tmlist e_ty in
    setType (TySeq(e_ty)) (TmSeq(ti,ty_ident,TmList(updated_tmlist),tmseq,ds_choice))
  | TmSeqMethod(ti,fun_name,actual_fun,args,arg_index,ds_choice,in_fix) ->
    setType (get_seq_fun_type fun_name (tm_info t)) (TmSeqMethod(ti,fun_name,actual_fun,args,arg_index,ds_choice,in_fix))
  | TmChar(ti,x) -> failwith "TODO TmChar (later)"
  | TmUC(ti,tree,ord,unique) -> failwith "TmUC (later)"
  | TmUtest(ti,t1,t2,t3) ->
    let t1'  = tc env TyDyn t1 in
    let t2'  = tc env TyDyn t2 in
    let ty1  = getType t1' in
    let ty2  = getType t2' in
    let (nty1,nty2) = (normTy ty1,normTy ty2) in
    let t3' = if tyequal nty1 nty2 then tc env TyDyn t3
              else errorUtestExp ti.fi nty1 nty2 in
    let ty3 = getType t3' in
    setType ty3 (TmUtest(ti,t1',t2',t3'))
  | TmMatch(ti,t1,cases) -> failwith "TODO TmMatch (later)"
  | TmNop -> TmNop

let get_tybody ty =
  match ty with
  | TyAll(_,_,_,ty) -> ty
  | _ -> ty

(* Erase type abstractions and applications *)
let rec erase t =
  let rec erase_list t_list =
    (match t_list with
     | [] -> []
     | hd::tl ->
       (erase hd)::(erase_list tl)) in
  match t with
  | TmVar(ti,x,n,pe) -> t
  | TmLam(ti,x,ty1,t1) -> TmLam(ti,x,ty1,erase t1)
  | TmClos(ti,s,ty,t1,env1,pe) -> failwith "Closer should not exist during erase."
  | TmApp(ti,t1,t2) ->
    let upd_app = TmApp(ti, erase t1, erase t2) in
    upd_app
  | TmConst(ti,c) -> t
  | TmIfexp(ti,cnd,thn,els) -> TmIfexp(ti, erase cnd, erase thn, erase els)
  | TmSeq(ti,ty_ident,tm_list,tm_seq,ds_choice) ->
    let upd_tm_list = TmList(erase_list (get_list_from_tmlist tm_list)) in
    TmSeq(ti,ty_ident,upd_tm_list,tm_seq,ds_choice)
  | TmSeqMethod _ ->
    t
  | TmFix(ti) -> t
  | TmTyLam(ti,x,kind,t1) -> erase t1
  | TmTyApp(ti,t1,ty1) ->
    let t1_tybody = get_tybody (getType t1) in
    let res = tySubst ty1 t1_tybody in
    setType (res) t1
  | TmChar(ti,x) -> t
  | TmUC(ti,tree,ord,unique) -> t
  | TmUtest(ti,t1,t2,t3) -> TmUtest(ti, erase t1, erase t2, erase t3)
  | TmMatch(ti,t1,cases) -> t (* TODO if needed *)
  | TmNop -> t


(* Main external function for type checking *)
let typecheck builtin t =
  (* Remove constant that are not supported by the type system *)
  let lst = List.filter
    (fun (x,_) ->
      match x with
      | "add" | "sub" | "div" | "mul" | "neg" |
        "dstr" | "dprint" | "print" | "argv" | "concat" -> false
      | _ -> true) builtin in
  (* Create type environment for builtins *)
  let tyenv = List.map (fun (x,c) -> TyenvTmvar(us x, type_const c)) lst in



  (* Testing merge function *)
  (*
  let int = TyGround(NoInfo,GInt) in
  let bool = TyGround(NoInfo,GBool) in
  let dyn = TyDyn in
  let arr t1 t2 = TyArrow(NoInfo,t1,t2) in
  let all t1 = TyAll(NoInfo,us"",KindStar(NoInfo),t1) in
  let var x n  = TyVar(NoInfo,us x,n) in
  let env = [TyenvTyvar(us"x",KindStar(NoInfo))] in
  let ty1 = all (arr dyn int) in
  let ty2 = all (arr int (var "x" 1))  in

  printf "\n------\n";
  (match tyMerge (all (arr int (var "x" 3))) (all (arr int bool)) with
  | None -> printf "None\n"
  | Some(ty') ->
    uprint_endline (pprint_ty ty');
  );
  printf "------\n";
  *)

  (* Type reconstruct *)
  let t_w_types = tc tyenv TyDyn t in

  (* Type check *)
  (*   let _ = typeOf tyenv t in *)
  t_w_types
