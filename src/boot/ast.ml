(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   File ast.ml includes the types and definitions for the abstract
   syntax tree (AST) of the bootstrap interpreter.
*)

open Ustring.Op
open Msg
open Linkedlist
open Ocamlarray
open Ocamlqueue
open Ocamlstack
open Okasakiqueue

let utest = ref false           (* Set to true if unit testing is enabled *)
let utest_ok = ref 0            (* Counts the number of successful unit tests *)
let utest_fail = ref 0          (* Counts the number of failed unit tests *)
let utest_fail_local = ref 0    (* Counts local failed tests for one file *)


(* Either an int, a float, or none *)
type intfloatoption =
| TInt   of int
| TFloat of float
| TNone

(* Evaluation environment *)
type env = tm list

and tinfo = {ety : ty option; fi : info}

(* Pattern used in match constructs *)
and pattern =
| PatIdent      of tinfo * ustring
| PatChar       of tinfo * int
| PatUC         of tinfo * pattern list * ucOrder * ucUniqueness
| PatBool       of tinfo * bool
| PatInt        of tinfo * int
| PatConcat     of tinfo * pattern * pattern

(* One pattern case *)
and case =
| Case          of tinfo * pattern * tm


(* Tree fore representing universal collection types (UCT) *)
and ucTree =
| UCNode        of ucTree * ucTree
| UCLeaf        of tm list


(* Properties of Universal Collection types *)
and ucOrder = UCUnordered | UCOrdered | UCSorted
and ucUniqueness = UCUnique | UCMultivalued

and const =
(* MCore intrinsic: Boolean constant and operations *)
| CBool of bool
| Cnot
| Cand  of bool option
| Cor   of bool option
(* MCore intrinsic: Integer constant and operations *)
| CInt  of int
| Caddi of int option
| Csubi of int option
| Cmuli of int option
| Cdivi of int option
| Cmodi of int option
| Cnegi
| Clti  of int option
| Cleqi of int option
| Cgti  of int option
| Cgeqi of int option
| Ceqi  of int option
| Cneqi of int option
| Cslli of int option
| Csrli of int option
| Csrai of int option
(* MCore intrinsic: Floating-point number constant and operations *)
| CFloat of float
| Caddf  of float option
| Csubf  of float option
| Cmulf  of float option
| Cdivf  of float option
| Cnegf
(* Mcore intrinsic: Polymorphic integer and floating-point numbers *)
| Cadd   of intfloatoption
| Csub   of intfloatoption
| Cmul   of intfloatoption
| Cdiv   of intfloatoption
| Cneg
(* MCore debug and I/O intrinsics *)
| CDStr
| CDPrint
| CPrint
| CArgv
(* MCore unified collection type (UCT) intrinsics *)
| CConcat of tm option

(* Atom - an untyped lable that can be used to implement
   domain specific constructs *)
| CAtom of sid * tm list

(* Tells if a variable is a pe variable or if a closure is a pe closure *)
and pemode = bool

and arg_index = int
and args = tm list
and ds_choice = int
and fun_name = ustring
and ty_ident = ustring
and in_fix = bool

and tm_list =
  | TmList   of tm list

and sequence =
  | SeqList  of tm Linkedlist.sequence
  | SeqQueue of tm Okasakiqueue.sequence
  | SeqOArray of tm Ocamlarray.sequence
  | SeqOQueue of tm Ocamlqueue.sequence
  | SeqOStack of tm Ocamlstack.sequence
  | SeqNone

and actual_fun =
  | SeqListFun1 of ((tm Linkedlist.sequence) -> (tm Linkedlist.sequence) -> (tm Linkedlist.sequence))
  | SeqListFun2 of ((tm Linkedlist.sequence) -> int)
  | SeqListFun3 of ((tm Linkedlist.sequence) -> tm -> (tm Linkedlist.sequence))
  | SeqListFun4 of ((tm Linkedlist.sequence) -> bool)
  | SeqListFun5 of ((tm Linkedlist.sequence) -> tm)
  | SeqListFun6 of ((tm Linkedlist.sequence) -> (tm Linkedlist.sequence))
  | SeqListFun7 of ((tm Linkedlist.sequence) -> int -> tm)
  | SeqListFun8 of ((tm Linkedlist.sequence) -> int -> (tm Linkedlist.sequence))
  | SeqListFun9 of ((tm -> tm) -> (tm Linkedlist.sequence) -> (tm Linkedlist.sequence))
  | SeqListFun10 of ((tm -> bool) -> (tm Linkedlist.sequence) -> bool)
  | SeqListFun11 of ((tm -> bool) -> (tm Linkedlist.sequence) -> tm)
  | SeqListFun12 of ((tm -> bool) -> (tm Linkedlist.sequence) -> (tm Linkedlist.sequence))
  | SeqListFun13 of ((tm -> tm -> tm) -> tm -> (tm Linkedlist.sequence) -> tm)
  | SeqQueueFun1 of ((tm Okasakiqueue.sequence) -> (tm Okasakiqueue.sequence) -> (tm Okasakiqueue.sequence))
  | SeqQueueFun2 of ((tm Okasakiqueue.sequence) -> int)
  | SeqQueueFun3 of ((tm Okasakiqueue.sequence) -> tm -> (tm Okasakiqueue.sequence))
  | SeqQueueFun4 of ((tm Okasakiqueue.sequence) -> bool)
  | SeqQueueFun5 of ((tm Okasakiqueue.sequence) -> tm)
  | SeqQueueFun6 of ((tm Okasakiqueue.sequence) -> (tm Okasakiqueue.sequence))
  | SeqQueueFun7 of ((tm Okasakiqueue.sequence) -> int -> tm)
  | SeqQueueFun8 of ((tm Okasakiqueue.sequence) -> int -> (tm Okasakiqueue.sequence))
  | SeqQueueFun9 of ((tm -> tm) -> (tm Okasakiqueue.sequence) -> (tm Okasakiqueue.sequence))
  | SeqQueueFun10 of ((tm -> bool) -> (tm Okasakiqueue.sequence) -> bool)
  | SeqQueueFun11 of ((tm -> bool) -> (tm Okasakiqueue.sequence) -> tm)
  | SeqQueueFun12 of ((tm -> bool) -> (tm Okasakiqueue.sequence) -> (tm Okasakiqueue.sequence))
  | SeqQueueFun13 of ((tm -> tm -> tm) -> tm -> (tm Okasakiqueue.sequence) -> tm)
  | SeqOArrayFun1 of ((tm Ocamlarray.sequence) -> (tm Ocamlarray.sequence) -> (tm Ocamlarray.sequence))
  | SeqOArrayFun2 of ((tm Ocamlarray.sequence) -> int)
  | SeqOArrayFun3 of ((tm Ocamlarray.sequence) -> tm -> (tm Ocamlarray.sequence))
  | SeqOArrayFun4 of ((tm Ocamlarray.sequence) -> bool)
  | SeqOArrayFun5 of ((tm Ocamlarray.sequence) -> tm)
  | SeqOArrayFun6 of ((tm Ocamlarray.sequence) -> (tm Ocamlarray.sequence))
  | SeqOArrayFun7 of ((tm Ocamlarray.sequence) -> int -> tm)
  | SeqOArrayFun8 of ((tm Ocamlarray.sequence) -> int -> (tm Ocamlarray.sequence))
  | SeqOArrayFun9 of ((tm -> tm) -> (tm Ocamlarray.sequence) -> (tm Ocamlarray.sequence))
  | SeqOArrayFun10 of ((tm -> bool) -> (tm Ocamlarray.sequence) -> bool)
  | SeqOArrayFun11 of ((tm -> bool) -> (tm Ocamlarray.sequence) -> tm)
  | SeqOArrayFun12 of ((tm -> bool) -> (tm Ocamlarray.sequence) -> (tm Ocamlarray.sequence))
  | SeqOArrayFun13 of ((tm -> tm -> tm) -> tm -> (tm Ocamlarray.sequence) -> tm)
  | SeqOQueueFun1 of ((tm Ocamlqueue.sequence) -> (tm Ocamlqueue.sequence) -> (tm Ocamlqueue.sequence))
  | SeqOQueueFun2 of ((tm Ocamlqueue.sequence) -> int)
  | SeqOQueueFun3 of ((tm Ocamlqueue.sequence) -> tm -> (tm Ocamlqueue.sequence))
  | SeqOQueueFun4 of ((tm Ocamlqueue.sequence) -> bool)
  | SeqOQueueFun5 of ((tm Ocamlqueue.sequence) -> tm)
  | SeqOQueueFun6 of ((tm Ocamlqueue.sequence) -> (tm Ocamlqueue.sequence))
  | SeqOQueueFun7 of ((tm Ocamlqueue.sequence) -> int -> tm)
  | SeqOQueueFun8 of ((tm Ocamlqueue.sequence) -> int -> (tm Ocamlqueue.sequence))
  | SeqOQueueFun9 of ((tm -> tm) -> (tm Ocamlqueue.sequence) -> (tm Ocamlqueue.sequence))
  | SeqOQueueFun10 of ((tm -> bool) -> (tm Ocamlqueue.sequence) -> bool)
  | SeqOQueueFun11 of ((tm -> bool) -> (tm Ocamlqueue.sequence) -> tm)
  | SeqOQueueFun12 of ((tm -> bool) -> (tm Ocamlqueue.sequence) -> (tm Ocamlqueue.sequence))
  | SeqOQueueFun13 of ((tm -> tm -> tm) -> tm -> (tm Ocamlqueue.sequence) -> tm)
  | SeqOStackFun1 of ((tm Ocamlstack.sequence) -> (tm Ocamlstack.sequence) -> (tm Ocamlstack.sequence))
  | SeqOStackFun2 of ((tm Ocamlstack.sequence) -> int)
  | SeqOStackFun3 of ((tm Ocamlstack.sequence) -> tm -> (tm Ocamlstack.sequence))
  | SeqOStackFun4 of ((tm Ocamlstack.sequence) -> bool)
  | SeqOStackFun5 of ((tm Ocamlstack.sequence) -> tm)
  | SeqOStackFun6 of ((tm Ocamlstack.sequence) -> (tm Ocamlstack.sequence))
  | SeqOStackFun7 of ((tm Ocamlstack.sequence) -> int -> tm)
  | SeqOStackFun8 of ((tm Ocamlstack.sequence) -> int -> (tm Ocamlstack.sequence))
  | SeqOStackFun9 of ((tm -> tm) -> (tm Ocamlstack.sequence) -> (tm Ocamlstack.sequence))
  | SeqOStackFun10 of ((tm -> bool) -> (tm Ocamlstack.sequence) -> bool)
  | SeqOStackFun11 of ((tm -> bool) -> (tm Ocamlstack.sequence) -> tm)
  | SeqOStackFun12 of ((tm -> bool) -> (tm Ocamlstack.sequence) -> (tm Ocamlstack.sequence))
  | SeqOStackFun13 of ((tm -> tm -> tm) -> tm -> (tm Ocamlstack.sequence) -> tm)
  | SeqFunNone

(* Terms / expressions *)
and tm =
| TmVar         of tinfo * ustring * int * pemode    (* Variable *)
| TmLam         of tinfo * ustring * ty * tm         (* Lambda abstraction *)
| TmClos        of tinfo * ustring * ty * tm * env * pemode (* Closure *)
| TmApp         of tinfo * tm * tm                   (* Application *)
| TmConst       of tinfo * const                     (* Constant *)
| TmIfexp       of tinfo * tm * tm * tm              (* If expression *)
| TmFix         of tinfo                             (* Fix point *)
| TmTyLam       of tinfo * ustring * kind * tm       (* Type abstraction *)
| TmTyApp       of tinfo * tm * ty                   (* Type application *)
| TmSeq         of tinfo * ty_ident * tm_list * sequence * ds_choice             (* Sequence constructor *)
| TmSeqMethod   of tinfo * fun_name * actual_fun * args * arg_index * ds_choice * in_fix (* Sequence method *)


| TmChar        of tinfo * int
| TmUC          of tinfo * ucTree * ucOrder * ucUniqueness
| TmUtest       of tinfo * tm * tm * tm
| TmMatch       of tinfo * tm * case list
| TmNop

(* Ground types *)
and groundty = GBool | GInt | GFloat | GVoid

(* Types *)
and ty =
| TyGround      of info * groundty                  (* Ground types *)
| TyArrow       of info * ty * ty                   (* Function type *)
| TyVar         of info * ustring * int             (* Type variable *)
| TyAll         of info * ustring * kind * ty       (* Universal type *)
| TyLam         of info * ustring * kind * ty       (* Type-level function *)
| TyApp         of info * ty * ty                   (* Type-level application *)
| TyDyn                                             (* Dynamic type *)
| TySeq         of ty (*element type*)

(* Kinds *)
and kind =
| KindStar      of info                             (* Kind of proper types *)
| KindArrow     of info * kind * kind               (* Kind of type-level functions *)


(* Variable type. Either a type variable or a term variable *)
and vartype =
| VarTy         of ustring
| VarTm         of ustring

and tyenvVar =
| TyenvTmvar    of ustring * ty
| TyenvTyvar    of ustring * kind                  (* Boolean states if it is
                                                       a forall binding *)

(* No index -1 means that de Bruijn index has not yet been assigned *)
let noidx = -1

(* Extract the variable name from a tyenvVar type *)
let envVar tyvar =
  match tyvar with TyenvTmvar(x,_) | TyenvTyvar(x,_) -> x

(* Returns the info field from a term *)
let tm_info t =
  match t with
  | TmVar({fi},_,_,_) -> fi
  | TmLam({fi},_,_,_) -> fi
  | TmClos({fi},_,_,_,_,_) -> fi
  | TmApp({fi},_,_) -> fi
  | TmConst({fi},_) -> fi
  | TmIfexp({fi},_,_,_) -> fi
  | TmFix({fi}) -> fi
  | TmTyLam({fi},_,_,_) -> fi
  | TmTyApp({fi},_,_) -> fi
  | TmSeq({fi},_,_,_,_) -> fi
  | TmSeqMethod({fi},_,_,_,_,_,_) -> fi

  | TmChar({fi},_) -> fi
  | TmUC({fi},_,_,_) -> fi
  | TmUtest({fi},_,_,_) -> fi
  | TmMatch({fi},_,_) -> fi
  | TmNop -> NoInfo

  (* Returns the info field from a term *)
let tm_tinfo t =
  match t with
  | TmVar(ti,_,_,_) -> ti
  | TmLam(ti,_,_,_) -> ti
  | TmClos(ti,_,_,_,_,_) -> ti
  | TmApp(ti,_,_) -> ti
  | TmConst(ti,_) -> ti
  | TmIfexp(ti,_,_,_) -> ti
  | TmFix(ti) -> ti
  | TmTyLam(ti,_,_,_) -> ti
  | TmTyApp(ti,_,_) -> ti
  | TmSeq(ti,_,_,_,_) -> ti
  | TmSeqMethod(ti,_,_,_,_,_,_) -> ti

  | TmChar(ti,_) -> ti
  | TmUC(ti,_,_,_) -> ti
  | TmUtest(ti,_,_,_) -> ti
  | TmMatch(ti,_,_) -> ti
  | TmNop -> failwith "No ti"


(* Returns the info field from a type *)
let ty_info t =
  match t with
  | TyGround(fi,_) -> fi
  | TyArrow(fi,_,_) -> fi
  | TyVar(fi,_,_) -> fi
  | TyAll(fi,_,_,_) -> fi
  | TyLam(fi,_,_,_) -> fi
  | TyApp(fi,_,_) -> fi
  | TyDyn -> NoInfo         (* Used when deriving types for let-expressions *)
  | TySeq _ -> NoInfo



(* Returns the info field from a kind *)
let kind_info k =
  match k with
  | KindStar(fi) -> fi
  | KindArrow(fi,_,_) -> fi


(* Returns the number of expected arguments *)
let arity c =
  match c with
  (* MCore intrinsic: Boolean constant and operations *)
  | CBool(_)    -> 0
  | Cnot        -> 1
  | Cand(None)  -> 2  | Cand(Some(_))  -> 1
  | Cor(None)   -> 2  | Cor(Some(_))   -> 1
  (* MCore intrinsic: Integer constant and operations *)
  | CInt(_)     -> 0
  | Caddi(None) -> 2  | Caddi(Some(_)) -> 1
  | Csubi(None) -> 2  | Csubi(Some(_)) -> 1
  | Cmuli(None) -> 2  | Cmuli(Some(_)) -> 1
  | Cdivi(None) -> 2  | Cdivi(Some(_)) -> 1
  | Cmodi(None) -> 2  | Cmodi(Some(_)) -> 1
  | Cnegi       -> 1
  | Clti(None)  -> 2  | Clti(Some(_))  -> 1
  | Cleqi(None) -> 2  | Cleqi(Some(_)) -> 1
  | Cgti(None)  -> 2  | Cgti(Some(_))  -> 1
  | Cgeqi(None) -> 2  | Cgeqi(Some(_)) -> 1
  | Ceqi(None)  -> 2  | Ceqi(Some(_))  -> 1
  | Cneqi(None) -> 2  | Cneqi(Some(_)) -> 1
  | Cslli(None) -> 2  | Cslli(Some(_)) -> 1
  | Csrli(None) -> 2  | Csrli(Some(_)) -> 1
  | Csrai(None) -> 2  | Csrai(Some(_)) -> 1
  (* MCore intrinsic: Floating-point number constant and operations *)
  | CFloat(_)   -> 0
  | Caddf(None) -> 2  | Caddf(Some(_)) -> 1
  | Csubf(None) -> 2  | Csubf(Some(_)) -> 1
  | Cmulf(None) -> 2  | Cmulf(Some(_)) -> 1
  | Cdivf(None) -> 2  | Cdivf(Some(_)) -> 1
  | Cnegf       -> 1
  (* Mcore intrinsic: Polymorphic integer and floating-point numbers *)
  | Cadd(TNone) -> 2  | Cadd(_)        -> 1
  | Csub(TNone) -> 2  | Csub(_)        -> 1
  | Cmul(TNone) -> 2  | Cmul(_)        -> 1
  | Cdiv(TNone) -> 2  | Cdiv(_)        -> 1
  | Cneg        -> 1
  (* MCore debug and I/O intrinsics *)
  | CDStr       -> 1
  | CDPrint     -> 1
  | CPrint      -> 1
  | CArgv       -> 1
  (* MCore unified collection type (UCT) intrinsics *)
  | CConcat(None)  -> 2  | CConcat(Some(_))  -> 1
  (* Atom - an untyped lable that can be used to implement
     domain specific constructs *)
  | CAtom(_,_)     -> 0


type 'a tokendata = {i:tinfo; v:'a}

let get_list_from_tmlist tm_l =
  match tm_l with
  | TmList(l) -> l


let ustring2uctm fi str =
  let lst = List.map (fun x -> TmChar({ety = None; fi = NoInfo},x)) (ustring2list str) in
  TmUC(fi,UCLeaf(lst),UCOrdered,UCMultivalued)
