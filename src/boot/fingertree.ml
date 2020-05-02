open Sequence
open Batteries

exception Empty
exception IndexOutOfBounds
exception NotFound

module Fingertree : Sequence = struct
  (* Constructors *)
  type 'a fingertree = Fin of 'a BatFingerTree.t | Nil

  type 'a sequence = 'a fingertree

  (*WC: O(1)*)
  let get_seq_name = "Finger Tree" (*O(1)*)

  (*WC: O(n)*)
  let to_list l = match l with
    | Fin(btf) -> BatFingerTree.to_list btf (*O(n)*)
    | _ -> [] (*O(1)*)

  (*WC: O(n)*)
  let from_list l = Fin(BatFingerTree.of_list l) (*O(n)*)

  (*WC: O(1)*)
  let empty = Fin(BatFingerTree.empty) (*O(1)*)

  (*WC: O(1)*)
  let is_empty l = match l with
    | Fin(btf) -> BatFingerTree.is_empty btf (*O(1)*)
    | _ -> true

  (*WC: O(1)*)
  let first l = match l with
    | Nil -> raise Empty
    | Fin(btf) -> (
        match BatFingerTree.head btf with (*O(1)*)
        | None -> raise Empty
        | Some hd -> hd
      )

  (*WC: O(1)*)
  let last l = match l with
    | Nil -> raise Empty
    | Fin(btf) -> (
        match BatFingerTree.last btf with (*O(1)*)
        | None -> raise Empty
        | Some e -> e
      )

  (*WC: O(1) TODO*)
  let push l e = match l with
    | Fin(btf) -> Fin(BatFingerTree.cons btf e) (*O(logn)*)
    | _ -> Fin(BatFingerTree.singleton e) (*O(1)*)

  (*WC: O(logn)*)
  let pop l = match l with
    | Nil -> raise Empty
    | Fin(btf) -> (
        match BatFingerTree.tail btf with (*O(logn)*)
        | None -> raise Empty
        | Some tl -> Fin(tl)
      )

  (*WC: O(1)*)
  let length l = match l with
    | Fin(btf) -> BatFingerTree.size btf (*O(1)*)
    | _ -> 0

  (*WC: O(logn)*)
  let nth l n = match l with
    | Fin(bft) -> BatFingerTree.get bft n (*O(logn)*)
    | Nil -> raise IndexOutOfBounds

  (*WC: O(log(min(n,m)))*)
  let append l1 l2 = match l1, l2 with
    | Nil, _ -> l2
    | _, Nil -> l1
    | Fin(bft1), Fin(bft2) -> Fin(BatFingerTree.append bft1 bft2) (*O(log(min(n,m)))*)

  (*WC: O(n)*)
  let reverse l = match l with
    | Fin(bft) -> Fin(BatFingerTree.reverse bft) (*O(n)*)
    | _ -> Nil

  (*O(1) TODO*)
  let push_last l e = match l with
    | Fin(bft) -> Fin(BatFingerTree.snoc bft e) (*O(logn)*)
    | _ -> Fin(BatFingerTree.singleton e) (*O(1)*)

  (*O(logn)*)
  let pop_last l = match l with
    | Nil -> raise Empty
    | Fin(bft) -> (
        match BatFingerTree.init bft with (*O(logn)*)
        | None -> raise Empty
        | Some bft2 -> Fin(bft2)
      )

  (*O(n * logn)*)
  let rec take_helper btf new_btf n i =
    if (i == (n)) then
      new_btf
    else (*snoc: O(logn), get O(logn)*)
      let new_new_btf = BatFingerTree.snoc new_btf (BatFingerTree.get btf i) in
      take_helper btf new_new_btf n (i+1)

  (*WC: O(n * logn)*)
  let take l n = match l, n with
    | Nil, 0 -> Nil
    | Nil, _ -> raise IndexOutOfBounds
    | Fin(btf), 0 -> Fin(BatFingerTree.empty) (*O(1)*)
    | Fin(btf), _ -> (
        if (n > BatFingerTree.size btf) then (*O(1)*)
          raise IndexOutOfBounds
        else
          Fin(take_helper btf (BatFingerTree.empty) n 0) (*O(1) + complexity for method*)
      )

  (*WC: O(n * logn)*)
  let rec drop l n = match l, n with
    | Nil, 0 -> Nil
    | Nil, _ -> raise IndexOutOfBounds
    | Fin(btf), 0 -> l
    | Fin(btf), _ -> (
        match BatFingerTree.tail btf with (*O(logn)*)
        | None -> raise IndexOutOfBounds
        | Some tl -> drop (Fin(tl)) (n-1) (*recursive*)
      )

  (*WC: O(n)*)
  let map f l = match l with
    | Fin(bft) -> Fin(BatFingerTree.map f bft) (*O(n)*)
    | Nil -> Nil

  (*WC: O(n * 1) TODO*)
  let rec any p l = match l with
    | Nil -> false
    | Fin(btf) -> (
        match BatFingerTree.head btf with (*O(1)*)
        | None -> false
        | Some hd -> (
            if p hd then
              true
            else
              (
                match BatFingerTree.tail btf with (*O(logn)*)
                | None -> false
                | Some tl -> any p (Fin(tl)) (*rec*)
              )
          )
      )

  (*WC: O(n * 1) TODO*)
  let rec check_if_all_true btf = match BatFingerTree.head btf with (*O(1)*)
    | None -> true
    | Some hd -> (
        if not hd then
          false
        else
          (match BatFingerTree.tail btf with (*O(logn)*)
           | None -> true
           | Some tl -> check_if_all_true tl
          )
      )

  (*O(n * 1 TODO)*)
  let all p l = match l with
    | Nil -> false
    | Fin(btf) -> (
        if BatFingerTree.is_empty btf then (*O(1)*)
          false
        else (
          let btf2 = BatFingerTree.map p btf in (*O(n)*)
          check_if_all_true btf2 (*O(n * 1 TODO)*)
        )
      )

  (*O(n * 1 TODO)*)
  let rec find p l = match l with
    | Nil -> raise NotFound
    | Fin(btf) -> (
        if BatFingerTree.is_empty btf then (*O(1)*)
          raise NotFound
        else (
          match BatFingerTree.head btf with (*O(1)*)
          | None -> raise NotFound
          | Some hd -> (
              if p hd then
                hd
              else
                (match BatFingerTree.tail btf with (*O(logn)*)
                 | None -> raise NotFound
                 | Some tl -> find p (Fin(tl))
                )
            )
        )
      )

  (*WC: O(n * logn)*)
  let rec filter_helper p btf new_btf n i =
    if (i == n) then
      new_btf
    else
      let e = BatFingerTree.get btf i in (*O(logn)*)
      if (p e) then
        let new_new_btf = BatFingerTree.snoc new_btf e in (*O(logn)*)
        filter_helper p btf new_new_btf n (i+1)
      else
        filter_helper p btf new_btf n (i+1)


  (*O(n * logn)*)
  let rec filter p l = match l with
    | Nil -> Nil
    | Fin(btf) -> Fin(filter_helper p btf (BatFingerTree.empty) (*O(1 + n * logn)*) (BatFingerTree.size btf) 0) (*O(1)*)

  (*O(n)*)
  let foldl f acc l = match l with
    | Nil -> acc
    | Fin(btf) -> BatFingerTree.fold_left f acc btf (*O(n)*)

  (*WC: O(n * logn)*)
  let rec foldr f acc l = match l with
    | Nil -> acc (*O(1)*)
    | Fin(btf) -> (
        (match BatFingerTree.head btf with (*O(1)*)
         | None -> acc
         | Some hd ->
           (match BatFingerTree.tail btf with (*O(logn)*)
            | None -> f hd acc
            | Some tl -> f hd (foldr f acc (Fin(tl)))
           )
        )
      )

  (*O(1) TODO*)
  let copy l = match l with
    | Fin(btf) -> Fin(btf)
    | _ -> Nil

end

open Fingertree
