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

  let rec pop_helper old_arr new_arr i =
    if (i == (Array.length old_arr)) then
      new_arr
    else
      let _ = Array.set new_arr (i-1) (Array.get old_arr i) in
      pop_helper old_arr new_arr (i+1)
  let rec reverse_helper old_arr new_arr i =
    if (i == (Array.length new_arr)) then
      new_arr
    else
      let _ = Array.set new_arr ((Array.length new_arr)-1) (Array.get old_arr i) in
      reverse_helper old_arr new_arr (i+1)
  let rec pop_last_helper old_arr new_arr i =
    if (i >= (Array.length old_arr)-1) then
      new_arr
    else
      let _ = Array.set new_arr i (Array.get old_arr i) in
      pop_last_helper old_arr new_arr (i+1)
  let rec take_helper old_arr new_arr n i =
    if (i == (n-1)) then
      new_arr
    else
      let _ = Array.set new_arr i (Array.get old_arr i) in
      take_helper old_arr new_arr n (i+1)
  let rec drop_helper old_arr new_arr n i =
    if (i == (Array.length old_arr)) then
      new_arr
    else
      let _ = Array.set new_arr (i-n) (Array.get old_arr i) in
      drop_helper old_arr new_arr n (i+1)
  let rec find_helper p arr i =
    if (i == (Array.length arr)) then
      raise NotFound
    else if (p (Array.get arr i)) then
      Array.get arr i
    else
      find_helper p arr (i+1)
  let rec filter_helper p old_arr new_arr i j =
    if (i == (Array.length old_arr)) then
      new_arr
    else if (p (Array.get old_arr i)) then
      let _ = Array.set new_arr j (Array.get old_arr i) in
      filter_helper p old_arr new_arr (i+1) (j+1)
    else
      filter_helper p old_arr new_arr (i+1) j

  let empty = Nil
  let is_empty arr =
    match arr with
    | Nil -> true
    | _ -> false
  let first arr =
    match arr with
    | Nil -> raise Empty
    | Arr(a) -> Array.get a 0
  let last arr =
    match arr with
    | Nil -> raise Empty
    | Arr(a) ->
      let last_i = (Array.length a) - 1 in
      Array.get a last_i
  let push arr e =
    match arr with
    | Nil -> Arr(Array.make 1 e)
    | Arr(a) ->
      let a_e = Array.make 1 e in
      Arr(Array.append a_e a)
  let pop arr =
    match arr with
    | Nil -> raise Empty
    | Arr(a) ->
      Arr(pop_helper a (Array.make ((Array.length a) - 1) (Array.get a 0)) 1)
  let length arr =
    match arr with
    | Nil -> 0
    | Arr(a) ->
      Array.length a
  let nth arr n =
    match arr with
    | Nil -> raise Empty
    | Arr(a) ->
      Array.get a n
  let append arr1 arr2 =
    match arr1, arr2 with
    | Nil, Nil -> Nil
    | Arr(a1), Nil -> arr1
    | Nil, Arr(a2) -> arr2
    | Arr(a1), Arr(a2) ->
      Arr(Array.append a1 a2)
  let reverse arr =
    match arr with
    | Nil -> Nil
    | Arr(a) ->
      Arr(reverse_helper a (Array.make (Array.length a) (Array.get a 0)) 0)
  let push_last arr e =
    match arr with
    | Nil -> Arr(Array.make 1 e)
    | Arr(a) ->
      let a_e = Array.make 1 e in
      let arr' = Array.append a a_e in
      Arr(arr')
  let pop_last arr =
    match arr with
    | Nil -> raise Empty
    | Arr(a) ->
      Arr(pop_last_helper a (Array.make (Array.length a) (Array.get a 0)) 0)
  let take arr n =
    match arr with
    | Nil -> raise Empty
    | Arr(a) ->
      Arr(take_helper a (Array.make (n) (Array.get a 0)) n 0)
  let drop arr n =
    match arr with
    | Nil -> raise Empty
    | Arr(a) ->
      Arr(drop_helper a (Array.make ((Array.length a) - n) (Array.get a 0)) n 0)
  let map f arr =
    match arr with
    | Nil -> raise Empty
    | Arr(a) ->
      Arr(Array.map f a)
  let any p arr =
    match arr with
    | Nil -> false
    | Arr(a) ->
      Array.exists p a
  let all p arr =
    match arr with
    | Nil -> false
    | Arr(a) ->
      Array.for_all p a
  let find p arr =
    match arr with
    | Nil -> raise Empty
    | Arr(a) ->
      find_helper p a 0
  let filter p arr =
    match arr with
    | Nil -> Nil
    | Arr(a) ->
      (*TODO: Ändra storlek på array*)
      Arr(filter_helper p a (Array.make (Array.length a) (Array.get a 0)) 0 0)
  let foldr f acc arr =
    match arr with
    | Nil -> acc
    | Arr(a) ->
      Array.fold_right f a acc
  let foldl f acc arr =
    match arr with
    | Nil -> acc
    | Arr(a) ->
      Array.fold_left f acc a
end

open Ocamlarray
