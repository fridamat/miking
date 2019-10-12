open Sequence

exception Empty
exception IndexOutOfBounds
exception NotFound

module Ocamlstack : Sequence = struct
  (* Constructors *)
  type 'a ocamlstack =
    | Nil
    | Sta of 'a Stack.t
  type 'a sequence = 'a ocamlstack

  let get_seq_name = "OCaml Stack"

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec from_list_helper l s =
    match l with
    | [] -> s
    | hd::tl ->
      let s' = from_list_helper tl s in (*Recursive call*)
      let _ = Stack.push hd s' in (*O(1)*)
      s'
  (*WC: O(N)*)
  let from_list l =
    match l with
    | [] ->
      Sta(Stack.create()) (*O(1)*)
    | _ ->
      let s = Stack.create() in (*O(1)*)
      Sta(from_list_helper l s) (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec to_list_helper s =
    if (Stack.is_empty s) then
      []
    else
      let e = Stack.pop s in (*O(1)*)
      e::(to_list_helper s) (*Recursive call*)
  (*WC: O(N)*)
  let to_list s =
    match s with
    | Nil -> []
    | Sta(s') ->
      to_list_helper s' (*O(N)*)

  (*WC: O(1)*)
  let empty = Nil

  (*WC: O(1)*)
  let is_empty s =
    match s with
    | Nil -> true
    | Sta(s') ->
      Stack.is_empty s' (*O(1)*)

  (*WC: O(1)*)
  let first s =
    match s with
    | Nil -> raise Empty
    | Sta(s') ->
      Stack.top s' (*O(1)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec last_helper s s_len i =
    if (i == (s_len - 1)) then
      Stack.pop s (*O(1)*)
    else
      let _ = Stack.pop s in (*O(1)*)
      last_helper s s_len (i + 1) (*Recursive call*)
  (*WC: O(N)*)
  let last s =
    match s with
    | Nil -> raise Empty
    | Sta(s') ->
      last_helper s' (Stack.length s') 0 (*Length: O(N), method call: O(N)*)

  (*WC: O(1)*)
  let push s e =
    match s with
    | Nil ->
      let s' = Stack.create() in (*O(1)*)
      let _ = Stack.push e s' in (*O(1)*)
      Sta(s')
    | Sta(s') ->
      let _ = Stack.push e s' in (*O(1)*)
      Sta(s')

  (*WC: O(1)*)
  let pop s =
    match s with
    | Nil -> raise Empty
    | Sta(s') ->
      let _ = Stack.pop s' in (*O(1)*)
      Sta(s')

  (*WC: O(N)*)
  let length s =
    match s with
    | Nil -> 0
    | Sta(s') ->
      Stack.length s' (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec nth_helper s n =
    if (n == 0) then
      Stack.pop s (*O(1)*)
    else
      let _ = Stack.pop s in (*O(1)*)
      nth_helper s (n - 1) (*Recursive call*)
  (*WC: O(N)*)
  let nth s n =
    match s with
    | Nil -> raise Empty
    | Sta(s') ->
      nth_helper s' n (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec append_helper s1 s2 =
    if (Stack.is_empty s1) then (*O(1)*)
      s2
    else
      let e = Stack.pop s1 in (*O(1)*)
      let s2' = append_helper s1 s2 in (*Recursive call*)
      let _ = Stack.push e s2' in (*O(1)*)
      s2'
  (*WC: O(N)*)
  let append s1 s2 =
    match s1, s2 with
    | Nil, Nil -> Nil
    | Nil, _ -> s2 (*O(1)*)
    | _, Nil -> s1 (*O(1)*)
    | Sta(s1'), Sta(s2') ->
      Sta(append_helper s1' s2') (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec reverse_helper s new_s =
    if (Stack.is_empty s) then (*O(1)*)
      new_s
    else
      let e = Stack.pop s in (*O(1)*)
      let _ = Stack.push e new_s in (*O(1)*)
      reverse_helper s new_s (*Recursive call*)
  (*WC: O(N)*)
  let reverse s =
    match s with
    | Nil -> Nil
    | Sta(s') ->
      let new_s = Stack.create() in (*=(1)*)
      Sta(reverse_helper s' new_s) (*O(N)*)

  (*WC: O(N)*)
  let push_last s e =
    match s with
    | Nil ->
      let s' = Stack.create() in (*O(1)*)
      let _ = Stack.push e s' in (*O(1)*)
      Sta(s')
    | Sta(s') ->
      let new_s = Stack.create() in (*O(1)*)
      let _ = Stack.push e new_s in (*O(1)*)
      append (Sta(s')) (Sta(new_s)) (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec pop_last_helper s new_s s_len i =
    if (i == (s_len - 1)) then
      new_s
    else
      let e = Stack.pop s in (*O(1)*)
      let new_s' = pop_last_helper s new_s s_len (i + 1) in (*Recursive call*)
      let _ = Stack.push e new_s' in (*O(1)*)
      new_s'
  (*WC: O(N)*)
  let pop_last s =
    match s with
    | Nil -> raise Empty
    | Sta(s') ->
      let new_s = Stack.create() in (*O(1)*)
      Sta(pop_last_helper s' new_s (Stack.length s') 0) (*Length: O(1), method call: O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec take_helper s new_s n i =
    if (i == n) then
      new_s
    else
      let e = Stack.pop s in (*O(1)*)
      let new_s' = take_helper s new_s n (i + 1) in (*Recursive call*)
      let _ = Stack.push e new_s' in (*O(1)*)
      new_s'
  (*WC: O(N)*)
  let take s n =
    match s with
    | Nil ->
      if (n == 0) then
        Nil
      else
        raise Empty
    | Sta(s') ->
      let new_s = Stack.create() in (*O(1)*)
      Sta(take_helper s' new_s n 0) (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec drop_helper s n i =
    if (i == n) then
      s
    else
      let _ = Stack.pop s in (*O(1)*)
      drop_helper s n (i + 1) (*Recursive call*)
  (*WC: O(N)*)
  let drop s n =
    match s with
    | Nil ->
      if (n == 0) then
        Nil
      else
        raise Empty
    | Sta(s') ->
      Sta(drop_helper s' n 0) (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N) ?Depends on the function?*)
  let rec map_helper f s new_s =
    if (Stack.is_empty s) then (*O(1)*)
      new_s
    else
      let e = Stack.pop s in (*O(1)*)
      let new_s' = map_helper f s new_s in (*Recursive call*)
      let e' = f e in (*?Depends on the function?*)
      let _ = Stack.push e' new_s' in (*O(1)*)
      new_s'
  (*WC: O(N)*)
  let map f s =
    match s with
    | Nil -> Nil
    | Sta(s') ->
      let new_s = Stack.create() in (*O(1)*)
      Sta(map_helper f s' new_s) (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec any_helper p s =
    if (Stack.is_empty s) then (*O(1)*)
      false
    else
      let e = Stack.pop s in (*O(1)*)
      if (p e) then (*?Depends on the function?*)
        true
      else
        any_helper p s (*Recursive call*)
  (*WC: O(N)*)
  let any p s =
    match s with
    | Nil -> false
    | Sta(s') ->
      any_helper p s' (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec all_helper p s =
    if (Stack.is_empty s) then (*O(1)*)
      true
    else
      let e = Stack.pop s in (*O(1)*)
      (p e) && (all_helper p s) (*Recursive call ?Depends on the function?*)
  (*WC: O(N)*)
  let all p s =
    match s with
    | Nil -> true
    | Sta(s') ->
      all_helper p s' (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N) ?Depends on the function?*)
  let rec find_helper p s =
    if (Stack.is_empty s) then (*O(1)*)
      raise NotFound
    else
      let e = Stack.pop s in (*O(1)*)
      if (p e) then (*?Depends on the function?*)
        e
      else
        find_helper p s (*Recursive call*)
  (*WC: O(N)*)
  let find p s =
    match s with
    | Nil -> raise NotFound
    | Sta(s') ->
      find_helper p s' (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N) ?Depends on the function? ?Am I right with two recursive calls?*)
  let rec filter_helper p s new_s =
    if (Stack.is_empty s) then (*O(N)*)
      new_s
    else
      let e = Stack.pop s in (*O(N)*)
      let new_s' = filter_helper p s new_s in (*Recursive call*)
      if (p e) then (*?Depends on the function?*)
        let _ = Stack.push e new_s' in (*O(1)*)
        filter_helper p s new_s' (*Recursive call*) (*???*)
      else
        filter_helper p s new_s' (*Recursive call*)
  (*WC: O(N)*)
  let filter p s =
    match s with
    | Nil -> Nil
    | Sta(s') ->
      let new_s = Stack.create() in (*O(1)*)
      Sta(filter_helper p s' new_s) (*O(N) ???*)

  (*WC: Each recursive call costs O(1) => O(N) ?Depends on the function?*)
  let rec foldr_helper f acc s =
    if (Stack.is_empty s) then (*O(1)*)
      acc
    else
      let e = Stack.pop s in (*O(1)*)
      f e (foldr_helper f acc s) (*Recursive call ?Depends on the function?*)
  (*WC: O(N)*)
  let foldr f acc s =
    match s with
    | Nil -> raise Empty
    | Sta(s') ->
      foldr_helper f acc s' (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N) ?Depends on the function?*)
  let rec foldl_helper f acc s =
    if (Stack.is_empty s) then (*O(1)*)
      acc
    else
      let e = Stack.pop s in (*O(1)*)
      foldl_helper f (f acc e) s (*Recursive call ?Depends on the function?*)
  (*WC: O(N)*)
  let foldl f acc s =
    match s with
    | Nil -> raise Empty
    | Sta(s') ->
      foldl_helper f acc s' (*O(N)*)
end

open Ocamlstack
