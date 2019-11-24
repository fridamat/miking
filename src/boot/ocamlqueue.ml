open Sequence

exception Empty
exception IndexOutOfBounds
exception NotFound

module Ocamlqueue : Sequence = struct
  (* Constructors *)
  type 'a ocamlqueue =
    | Nil
    | Que of 'a Queue.t
  type 'a sequence = 'a ocamlqueue

  let get_seq_name = "OCaml Queue"

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec from_list_helper l q =
    match l with
    | [] -> q
    | hd::tl ->
      let _ = Queue.add hd q in (*O(1)*)
      from_list_helper tl q (*Recursive call*)
  (*WC: O(N)*)
  let from_list l =
    let q = Queue.create() in (*O(1)*)
    Que(from_list_helper l q) (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec to_list_helper q =
    if (Queue.is_empty q) then (*O(1)*)
      []
    else
      let e = Queue.pop q in (*O(1)*)
      e::(to_list_helper q) (*Recursive call*)
  (*WC: O(N)*)
  let to_list q =
    match q with
    | Nil -> []
    | Que(q') ->
      if (Queue.is_empty q') then (*O(1)*)
        []
      else
        let q_copy = Queue.copy q' in (*O(N)*)
        to_list_helper q_copy (*O(N)*)

  (*WC: O(1)*)
  let empty = Nil

  (*WC: O(1)*)
  let is_empty q =
    match q with
    | Nil -> true
    | Que(q') ->
      Queue.is_empty q' (*O(1)*)

  (*WC: O(1)*)
  let first q =
    match q with
    | Nil -> raise Empty
    | Que(q') ->
      if Queue.is_empty q' then
        raise Empty
      else
        let q_copy = Queue.copy q' in
        Queue.take q_copy (*O(1)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec last_helper q =
    if (Queue.is_empty q) then (*O(1)*)
      raise Empty
    else if (Queue.length q == 1) then (*O(1)*)
      Queue.pop q (*O(1)*)
    else
      let _ = Queue.pop q in (*O(1)*)
      last_helper q (*Recursive call*)
  (*WC: O(N)*)
  let last q =
    match q with
    | Nil -> raise Empty
    | Que(q') ->
      if Queue.is_empty q' then
        raise Empty
      else
        let q_copy = Queue.copy q' in (*O(N)*)
        last_helper q_copy

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec push_helper q new_q =
    if (Queue.is_empty q) then (*O(1)*)
      new_q
    else
      let e = Queue.pop q in (*O(1)*)
      let _ = Queue.add e new_q in (*O(1)*)
      push_helper q new_q (*Recursive call*)
  (*WC: O(N)*)
  let push q e =
    match q with
    | Nil ->
      let q' = Queue.create() in (*O(1)*)
      let _ = Queue.add e q' in (*O(1)*)
      Que(q')
    | Que(q') ->
      let new_q = Queue.create() in (*O(1)*)
      let _ = Queue.add e new_q in (*O(1)*)
      let q_copy = Queue.copy q' in
      Que(push_helper q_copy new_q) (*O(N)*)

  (*WC: O(N)*)
  let pop q =
    match q with
    | Nil -> raise Empty
    | Que(q') ->
      if Queue.is_empty q' then
        raise Empty
      else
        let q_copy = Queue.copy q' in (*O(N)*)
        let _ = Queue.pop q_copy in (*O(1)*)
        Que(q_copy)

  (*WC: O(1)*)
  let length q =
    match q with
    | Nil -> 0
    | Que(q') ->
      Queue.length q' (*O(1)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec nth_helper q n =
    if (n == 0) then
      Queue.pop q (*O(1)*)
    else
      let _ = Queue.pop q in (*O(1)*)
      nth_helper q (n - 1) (*Recursive call*)
  (*WC: O(N)*)
  let nth q n =
    match q with
    | Nil -> raise IndexOutOfBounds
    | Que(q') ->
      if (n < 0) || (n >= Queue.length q')
      then
        raise IndexOutOfBounds
      else
        let q_copy = Queue.copy q' in (*O(N)*)
        nth_helper q_copy n (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec append_helper q1 q2 =
    if Queue.is_empty q2 then (*O(1)*)
      q1
    else
      let e = Queue.pop q2 in (*O(1)*)
      let _ = Queue.add e q1 in (*O(1)*)
      append_helper q1 q2 (*Recursive call*)
  (*WC: O(N)*)
  let append q1 q2 =
    match q1, q2 with
    | Nil, Nil -> Nil
    | Nil, _ -> q2
    | _, Nil -> q1
    | Que(q1'), Que(q2') ->
      let q1_copy = Queue.copy q1' in (*O(N)*)
      let q2_copy = Queue.copy q2' in (*O(N)*)
      Que(append_helper q1_copy q2_copy) (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec reverse_helper q new_q =
    if Queue.is_empty q then (*O(1)*)
      new_q
    else
      let e = Queue.pop q in (*O(1)*)
      let _ = Queue.add e new_q in (*O(1)*)
      reverse_helper q new_q (*Recursive call*)
  (*WC: O(N)*)
  let reverse q =
    match q with
    | Nil -> Nil
    | Que(q') ->
      let q_copy = Queue.copy q' in (*O(N)*)
      Que(reverse_helper q_copy (Queue.create())) (*O(N)*)

  (*WC: O(N)*)
  let push_last q e =
    match q with
    | Nil ->
      let q' = Queue.create() in (*O(1)*)
      let _ = Queue.add e q' in (*O(1)*)
      Que(q')
    | Que(q') ->
      let q_copy = Queue.copy q' in (*O(N)*)
      let _ = Queue.add e q_copy in (*O(1)*)
      Que(q_copy) (*O(1)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec pop_last_helper q new_q q_len i =
    if (i == (q_len - 1)) then
      new_q
    else
      let e = Queue.pop q in (*O(1)*)
      let _ = Queue.add e new_q in (*O(1)*)
      pop_last_helper q new_q q_len (i + 1) (*Recursive call*)
  (*WC: O(N)*)
  let pop_last q =
    match q with
    | Nil -> raise Empty
    | Que(q') ->
      if Queue.is_empty q' then
        raise Empty
      else
        let new_q = Queue.create() in (*O(1)*)
        let q_copy = Queue.copy q' in (*O(N)*)
        Que(pop_last_helper q_copy new_q (Queue.length q') 0) (*Length: O(1), method call: O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec take_helper q new_q n =
    if (n == 0) then
      new_q
    else
      let e = Queue.pop q in (*O(1)*)
      let _ = Queue.add e new_q in (*O(1)*)
      take_helper q new_q (n - 1) (*Recursive call*)
  (*WC: O(N)*)
  let take q n =
    match q with
    | Nil ->
      if (n == 0) then
        Nil
      else
        raise IndexOutOfBounds
    | Que(q') ->
      if (n < 0) || (n > Queue.length q') then
        raise IndexOutOfBounds
      else
        let new_q = Queue.create() in (*O(1)*)
        let q_copy = Queue.copy q' in (*O(N)*)
        Que(take_helper q_copy new_q n) (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec drop_helper q n =
    if (n == 0) then
      q
    else
      let _ = Queue.pop q in (*O(1)*)
      drop_helper q (n - 1) (*Recursive call*)
  (*WC: O(N)*)
  let drop q n =
    match q with
    | Nil ->
      if (n == 0) then
        Nil
      else
        raise IndexOutOfBounds
    | Que(q') ->
      if (n < 0) || (n > Queue.length q') then
        raise IndexOutOfBounds
      else
        let q_copy = Queue.copy q' in (*O(N)*)
        Que(drop_helper q_copy n) (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N) ?Depends on function?*)
  let rec map_helper f q new_q =
    if (Queue.is_empty q) then (*O(1)*)
      new_q
    else
      let e = Queue.pop q in (*O(1)*)
      let e' = f e in (*?Depends on the function?*)
      let _ = Queue.add e' new_q in (*O(1)*)
      map_helper f q new_q (*Recursive call*)
  (*WC: O(N)*)
  let map f q =
    match q with
    | Nil -> Nil
    | Que(q') ->
      if Queue.is_empty q' then
        Nil
      else
        let new_q = Queue.create() in (*O(1)*)
        let q_copy = Queue.copy q' in (*O(N)*)
        Que(map_helper f q_copy new_q) (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N) ?Depends on the function?*)
  let rec any_helper p q =
    if (Queue.is_empty q) then (*O(1)*)
      false
    else
      let e = Queue.pop q in (*O(1)*)
      if (p e) then (*?Depends on the function?*)
        true
      else
        any_helper p q (*Recursive call*)
  (*O(N)*)
  let any p q =
    match q with
    | Nil -> false
    | Que(q') ->
      if Queue.is_empty q' then
        false
      else
        let q_copy = Queue.copy q' in
        any_helper p q_copy (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N) ?Depends on the function?*)
  let rec all_helper p q =
    if (Queue.is_empty q) then (*O(1)*)
      true
    else
      let e = Queue.pop q in (*O(1)*)
      (p e) && (all_helper p q) (*Recursive call ?Depends on the function?*)
  (*WC: O(N)*)
  let all p q =
    match q with
    | Nil -> false
    | Que(q') ->
      if Queue.is_empty q' then
        false
      else
        let q_copy = Queue.copy q' in
        all_helper p q_copy (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec find_helper p q =
    if (Queue.is_empty q) then (*O(1)*)
      raise NotFound
    else
      let e = Queue.pop q in (*O(1)*)
      if (p e) then (*?Depends on the function?*)
        e
      else
        find_helper p q (*Recursive call*)
  (*WC: O(N)*)
  let find p q =
    match q with
    | Nil ->
      raise NotFound
    | Que(q') ->
      let q_copy = Queue.copy q' in (*O(N)*)
      find_helper p q_copy (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N)*)
  let rec filter_helper p q new_q =
    if (Queue.is_empty q) then (*O(1)*)
      new_q
    else
      let e = Queue.pop q in (*O(1)*)
      if (p e) then (*?Depends on the function?*)
        let _ = Queue.add e new_q in (*O(1)*)
        filter_helper p q new_q (*Recursive call*)
      else
        filter_helper p q new_q (*Recursive call*)
  (*WC: O(N)*)
  let filter p q =
    match q with
    | Nil -> Nil
    | Que(q') ->
      let new_q = Queue.create() in (*O(1)*)
      let q_copy = Queue.copy q' in (*O(N)*)
      Que(filter_helper p q_copy new_q) (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N) ?Depends on function?*)
  let rec foldr_helper f acc q =
    if (Queue.is_empty q) then (*O(1)*)
      acc
    else
      let e = Queue.pop q in (*O(1)*)
      f e (foldr_helper f acc q) (*Recursive call ?Depends on function?*)
  (*WC: O(N)*)
  let foldr f acc q =
    match q with
    | Nil -> acc
    | Que(q') ->
      if Queue.is_empty q' then
        acc
      else
        let q_copy = Queue.copy q' in (*O(N)*)
        foldr_helper f acc q_copy (*O(N)*)

  (*WC: Each recursive call costs O(1) => O(N) ?Depends on function?*)
  let rec foldl_helper f acc q =
    if (Queue.is_empty q) then (*O(1)*)
      acc
    else
      let e = Queue.pop q in (*O(1)*)
      foldl_helper f (f acc e) q (*Recursive call ?Depends on function?*)
  (*WC: O(N)*)
  let foldl f acc q =
    match q with
    | Nil -> raise Empty
    | Que(q') ->
      if Queue.is_empty q' then
        acc
      else
        let q_copy = Queue.copy q' in (*O(N)*)
        foldl_helper f acc q_copy (*O(N)*)

  (*WC: O(N)*)
  let rec copy q =
    match q with
    | Nil -> Nil
    | Que(q') ->
      Que(Queue.copy q')
end

open Ocamlqueue
