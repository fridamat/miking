open Sequence
open Batteries

exception Empty
exception IndexOutOfBounds
exception NotFound

module Fingertree : Sequence = struct
  (* Constructors *)
  type 'a fingertree = Fin of 'a BatFingerTree.t | Nil

  type 'a sequence = 'a fingertree

  let get_seq_name = "Finger Tree"

  let to_list l = match l with
    | Fin(btf) -> BatFingerTree.to_list btf (*O(n)*)
    | _ -> []

  let from_list l = Fin(BatFingerTree.of_list l) (*O(n)*)

  let empty = Fin(BatFingerTree.empty)

  let is_empty l = match l with
    | Fin(btf) -> BatFingerTree.is_empty btf
    | _ -> true

  let first l = match l with
    | Nil -> raise Empty
    | Fin(btf) -> (
        match BatFingerTree.head btf with (*O(1)*)
        | None -> raise Empty
        | Some hd -> hd
      )

  let rec last l = match l with
    | Nil -> raise Empty
    | Fin(btf) -> (
        match BatFingerTree.last btf with (*O(1)*)
        | None -> raise Empty
        | Some e -> e
      )

  let push l e = match l with
    | Fin(btf) -> Fin(BatFingerTree.cons btf e) (*O(logn)*)
    | _ -> Fin(BatFingerTree.singleton e) (*O(1)*)

  let pop l = match l with
    | Nil -> raise Empty
    | Fin(btf) -> (
        match BatFingerTree.tail btf with (*O(logn)*)
        | None -> raise Empty
        | Some tl -> Fin(tl)
      )

  let rec length l = match l with
    | Fin(btf) -> BatFingerTree.size btf (*O(n)*)
    | _ -> 0

  let rec nth l n = match l with
    | Fin(bft) -> BatFingerTree.get bft n (*O(logn)*)
    | Nil -> raise IndexOutOfBounds

  let rec append l1 l2 = match l1, l2 with
    | Nil, _ -> l2
    | _, Nil -> l1
    | Fin(bft1), Fin(bft2) -> Fin(BatFingerTree.append bft1 bft2) (*O(log(min(n,m)))*)

  let reverse l = match l with
    | Fin(bft) -> Fin(BatFingerTree.reverse bft)
    | _ -> Nil

  let rec push_last l e = match l with
    | Fin(bft) -> Fin(BatFingerTree.snoc bft e) (*O(logn)*)
    | _ -> Fin(BatFingerTree.singleton e) (*O(1)*)

  let rec pop_last l = match l with
    | Nil -> raise Empty
    | Fin(bft) -> (
        match BatFingerTree.init bft with
        | None -> raise Empty
        | Some bft2 -> Fin(bft2)
      )

  let rec take_helper btf new_btf n i =
    if (i == (n)) then
      new_btf
    else
      let new_new_btf = BatFingerTree.snoc new_btf (BatFingerTree.get btf i) in
      take_helper btf new_new_btf n (i+1)

  let take l n = match l, n with
    | Nil, 0 -> Nil
    | Nil, _ -> raise IndexOutOfBounds
    | Fin(btf), 0 -> Fin(BatFingerTree.empty)
    | Fin(btf), _ -> (
        if (n > BatFingerTree.size btf) then
          raise IndexOutOfBounds
        else
          Fin(take_helper btf (BatFingerTree.empty) n 0)
      )

  let rec drop l n = match l, n with
    | Nil, 0 -> Nil
    | Nil, _ -> raise IndexOutOfBounds
    | Fin(btf), 0 -> l
    | Fin(btf), _ -> (
        match BatFingerTree.tail btf with
        | None -> raise IndexOutOfBounds
        | Some tl -> drop (Fin(tl)) (n-1)
      )

  let rec map f l = match l with
    | Fin(bft) -> Fin(BatFingerTree.map f bft)
    | Nil -> Nil

  let rec any p l = match l with
    | Nil -> false
    | Fin(btf) -> (
        match BatFingerTree.head btf with
        | None -> false
        | Some hd -> (
            if p hd then
              true
            else
              (
                match BatFingerTree.tail btf with
                | None -> false
                | Some tl -> any p (Fin(tl))
              )
          )
      )

  let rec check_if_all_true btf = match BatFingerTree.head btf with
    | None -> true
    | Some hd -> (
        if not hd then
          false
        else
          (match BatFingerTree.tail btf with
           | None -> true
           | Some tl -> check_if_all_true tl
          )
      )

  let all p l = match l with
    | Nil -> false
    | Fin(btf) -> (
        if BatFingerTree.is_empty btf then
          false
        else (
          let btf2 = BatFingerTree.map p btf in
          check_if_all_true btf2
        )
      )

  let rec find p l = match l with
    | Nil -> raise NotFound
    | Fin(btf) -> (
        if BatFingerTree.is_empty btf then
          raise NotFound
        else (
          match BatFingerTree.head btf with
          | None -> raise NotFound
          | Some hd -> (
              if p hd then
                hd
              else
                (match BatFingerTree.tail btf with
                 | None -> raise NotFound
                 | Some tl -> find p (Fin(tl))
                )
            )
        )
      )

  let rec filter_helper p btf new_btf n i =
    if (i == n) then
      new_btf
    else
      let e = BatFingerTree.get btf i in
      if (p e) then
        let new_new_btf = BatFingerTree.snoc new_btf e in
        filter_helper p btf new_new_btf n (i+1)
      else
        filter_helper p btf new_btf n (i+1)


  let rec filter p l = match l with
    | Nil -> Nil
    | Fin(btf) -> Fin(filter_helper p btf (BatFingerTree.empty) (BatFingerTree.size btf) 0)

  let foldl f acc l = match l with
    | Nil -> acc
    | Fin(btf) -> BatFingerTree.fold_left f acc btf

  let rec foldr f acc l = match l with
    | Nil -> acc (*O(1)*)
    | Fin(btf) -> (
        (match BatFingerTree.head btf with
         | None -> acc
         | Some hd ->
           (match BatFingerTree.tail btf with
            | None -> f hd acc
            | Some tl -> f hd (foldr f acc (Fin(tl)))
           )
        )
      )

  let copy l = match l with
    | Fin(btf) -> Fin(btf)
    | _ -> Nil

end

open Fingertree
