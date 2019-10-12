open Sequence

exception Empty
exception IndexOutOfBounds
exception NotFound

module Ocamlarray : Sequence = struct
  (* Constructors *)
  type 'a ocamlarray = Arr of 'a array | Nil

  type 'a sequence = 'a ocamlarray

  let get_seq_name = "OCaml Array"

  let from_list l =
    match l with
    | [] -> Nil
    | _ -> Arr(Array.of_list l)
  let rec to_list arr =
    match arr with
    | Nil -> []
    | Arr(a) -> Array.to_list a
  (*WC: O(1) for each recursive call, so O(N)*)
  let rec pop_helper old_arr new_arr i =
    if (i == (Array.length old_arr)) then (*O(1)*)
      new_arr
    else
      let _ = Array.set new_arr (i-1) (Array.get old_arr i) in (*O(1)*)
      pop_helper old_arr new_arr (i+1) (*Recursive*)
  (*WC: O(1) for each recursive call, so O(N)*)
  let rec reverse_helper old_arr new_arr i =
    if (i == (Array.length new_arr)) then (*O(1)*)
      new_arr
    else
      let _ = Array.set new_arr ((Array.length new_arr)-1) (Array.get old_arr i) in (*3 x O(1)*)
      reverse_helper old_arr new_arr (i+1) (*Recursive*)
  (*WC: O(1) for each recursive call, so O(N)*)
  let rec pop_last_helper old_arr new_arr i =
    if (i >= (Array.length old_arr)-1) then (*O(1)*)
      new_arr
    else
      let _ = Array.set new_arr i (Array.get old_arr i) in (*2 x O(1)*)
      pop_last_helper old_arr new_arr (i+1) (*Recursive*)
  (*WC: O(1) for each recursive call, so O(N)*)
  let rec take_helper old_arr new_arr n i =
    if (i == n) then
      new_arr
    else
      let _ = Array.set new_arr i (Array.get old_arr i) in (*2 x O(1)*)
      take_helper old_arr new_arr n (i+1) (*Recursive*)
  (*WC: O(1) for each recursive call, so O(N)*)
  let rec drop_helper old_arr new_arr n i =
    if (i == (Array.length old_arr)) then (*O(1)*)
      new_arr
    else if (i >= n) then
      let _ = Array.set new_arr (i-n) (Array.get old_arr i) in (*2 x O(1)*)
      drop_helper old_arr new_arr n (i+1) (*Recursive*)
    else
      drop_helper old_arr new_arr n (i+1) (*Recursive*)
  (*WC: O(1) for each recursive call, so O(N)*)
  let rec find_helper p arr i =
    if (i == (Array.length arr)) then (*O(1)*)
      raise NotFound
    else if (p (Array.get arr i)) then (*O(1)*)
      Array.get arr i (*O(1)*)
    else
      find_helper p arr (i+1) (*Recursive*)
  (*WC: Since we have an append in each recursive call: O(N^2)*)
  let rec filter_helper p old_arr new_arr i j =
    if (i == (Array.length old_arr)) then (*O(1)*)
      new_arr
    else if (p (Array.get old_arr i)) then (*O(1)*)
      let new_arr' = Array.make 1 (Array.get old_arr i) in (*2 x O(1)*)
      filter_helper p old_arr (Array.append new_arr new_arr') (i+1) (j+1) (*O(#elements currently), recursive*)
    else
      filter_helper p old_arr new_arr (i+1) j (*Recursive*)

  (*WC: O(1)*)
  let empty = Nil
  (*WC: O(1)*)
  let is_empty arr =
    match arr with
    | Nil -> true
    | _ -> false
  (*WC: O(1)*)
  let first arr =
    match arr with
    | Nil -> raise Empty
    | Arr(a) -> Array.get a 0
  (*WC: O(1)*)
  let last arr =
    match arr with
    | Nil -> raise Empty
    | Arr(a) ->
      let last_i = (Array.length a) - 1 in (*O(1)*)
      Array.get a last_i (*O(1)*)
  (*WC: O(N)*)
  let push arr e =
    match arr with
    | Nil -> Arr(Array.make 1 e)
    | Arr(a) ->
      let a_e = Array.make 1 e in
      Arr(Array.append a_e a)
  (*WC: O(N)*)
  let pop arr =
    match arr with
    | Nil -> raise Empty
    | Arr(a) ->
      Arr(pop_helper a (Array.make ((Array.length a) - 1) (Array.get a 0)) 1) (*O(N) - Creating and populating the new array*)
  (*WC: O(1)*)
  let length arr =
    match arr with
    | Nil -> 0
    | Arr(a) ->
      Array.length a (*O(1)*)
  (*WC: O(1)*)
  let nth arr n =
    match arr with
    | Nil -> raise Empty
    | Arr(a) ->
      Array.get a n (*O(1)*)
  (*WC: O(N)*)
  let append arr1 arr2 =
    match arr1, arr2 with
    | Nil, Nil -> Nil
    | Arr(a1), Nil -> arr1 (*O(1)*)
    | Nil, Arr(a2) -> arr2 (*O(1)*)
    | Arr(a1), Arr(a2) ->
      Arr(Array.append a1 a2) (*O(N)*)
  (*WC: O(N)*)
  let reverse arr =
    match arr with
    | Nil -> Nil
    | Arr(a) ->
      Arr(reverse_helper a (Array.make (Array.length a) (Array.get a 0)) 0) (*Creating new array: O(N), call method O(N)*)
  (*WC: O(N)*)
  let push_last arr e =
    match arr with
    | Nil -> Arr(Array.make 1 e)
    | Arr(a) ->
      let a_e = Array.make 1 e in
      let arr' = Array.append a a_e in (*O(N)*)
      Arr(arr')
  (*WC: O(N)*)
  let pop_last arr =
    match arr with
    | Nil -> raise Empty
    | Arr(a) ->
      Arr(pop_last_helper a (Array.make ((Array.length a) - 1) (Array.get a 0)) 0) (*Creating array: O(N), method call O(N)*)
  (*WC: O(N)*)
  let take arr n =
    match arr, n with
    | Nil, _ -> raise Empty
    | _, 0 -> Nil
    | Arr(a), _ ->
      Arr(take_helper a (Array.make n (Array.get a 0)) n 0) (*Creating array: O(N), method call O(N)*)
  let drop arr n =
    match arr, n with
    | _, 0 -> arr
    | Nil, _ -> raise Empty
    | Arr(a), _ ->
      Arr(drop_helper a (Array.make ((Array.length a) - n) (Array.get a 0)) n 0) (*Creating array: O(N), method call O(N)*)
  (*WC: O(N)*)
  let map f arr =
    match arr with
    | Nil -> raise Empty
    | Arr(a) ->
      Arr(Array.map f a) (*Accessing each element => O(N)*)
  (*WC: O(N)*)
  let any p arr =
    match arr with
    | Nil -> false
    | Arr(a) ->
      Array.exists p a (*Finding an element => O(N)*)
  (*WC: O(N)*)
  let all p arr =
    match arr with
    | Nil -> false
    | Arr(a) ->
      Array.for_all p a
  (*WC: O(N)*)
  let find p arr =
    match arr with
    | Nil -> raise Empty
    | Arr(a) ->
      find_helper p a 0 (*Finding an element => O(N)*)
  (*WC: O(N^2)*)
  let filter p arr =
    match arr with
    | Nil -> Nil
    | Arr(a) ->
      Arr((filter_helper p a (Array.make 0 (Array.get a 0)) 0 0)) (*Method call O(N^2)*)
  (*WC: O(N)*)
  let foldr f acc arr =
    match arr with
    | Nil -> acc
    | Arr(a) ->
      Array.fold_right f a acc
  (*WC: O(N)*)
  let foldl f acc arr =
    match arr with
    | Nil -> acc
    | Arr(a) ->
      Array.fold_left f acc a
end

open Ocamlarray
