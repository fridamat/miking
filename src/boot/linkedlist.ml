open Sequence

exception Empty
exception IndexOutOfBounds

module Linkedlist : Sequence = struct
  (* Constructors *)
  type 'a linkedlist =
   | Nil
   | Cons of 'a * 'a linkedlist

  type 'a sequence = 'a linkedlist

  let get_seq_name = "Linked List"

  let rec from_list = function
    | [] -> Nil
    | hd::tl -> Cons(hd, from_list tl)
  let rec to_list = function
    | Nil -> []
    | Cons(hd,tl) -> hd::(to_list tl)

  (* Helper methods *)
    let rec reverse_helper l rev_l = match l with (*TODO error if Linkedlist is empty from beginning?*)
    | Nil -> rev_l
    | Cons(hd, tl) -> reverse_helper tl (Cons(hd, rev_l))

  let empty = Nil
  let is_empty = function
    | Nil -> true
    | _ -> false
  let first = function
    | Nil -> raise Empty
    | Cons(hd, _) -> hd
  let rec last = function
    | Nil -> raise Empty
    | Cons(hd, Nil) -> hd
    | Cons(_, tl) -> last tl
  let push l e = Cons(e, l)
  let pop = function
    | Nil -> raise Empty
    | Cons(hd, tl) -> tl
  let rec length = function
    | Nil -> 0
    | Cons(_, tl) -> 1 + length tl
  let rec nth l n = match (l, n) with (*TODO Check if n <= 0*)
    | (Nil, _) -> raise IndexOutOfBounds
    | (Cons(hd,_), 0) -> hd (*TODO: Should this be indexed by zero?*)
    | (Cons(_,tl), _) -> nth tl (n-1)
  let rec append l1 l2 = match l1 with
    | Nil -> l2
    | Cons(hd,tl) -> Cons(hd, (append tl l2))
  let reverse l = reverse_helper l Nil
  let rec push_last l e = match l with
    | Nil -> Cons(e, Nil)
    | Cons(hd,tl) -> Cons(hd, (push_last tl e))
  let rec pop_last = function
    | Nil -> raise Empty
    | Cons(hd,Nil) -> Nil
    | Cons(hd,tl) -> Cons(hd, (pop_last tl))
  let rec take l n = match l, n with
    | Nil, _ -> raise IndexOutOfBounds
    | _, 0 -> Nil
    | Cons(hd,_), 1 -> Cons(hd, Nil)
    | Cons(hd,tl), _ -> Cons(hd, (take tl (n-1)))
  let rec drop l n = match l, n with
    | _, 0 -> l
    | Nil, _ -> raise IndexOutOfBounds
    | Cons(_,tl), _ -> drop tl (n-1)
  let rec map f = function
    | Nil -> Nil
    | Cons(hd, tl) -> Cons(f hd, map f tl)
  let rec any p = function
    | Nil -> false
    | Cons(hd, tl) -> p hd || any p tl
  let rec all p = function
    | Nil -> true
    | Cons(hd, tl) -> p hd && all p tl
  let rec find p = function
    | Nil -> None (*raise NotFound?*) (*TODO: Should we get something else???*)
    | Cons(hd, tl) ->
      (match p hd with
       | true -> Some hd
       | false -> find p tl)
  let rec filter p = function
    | Nil -> Nil
    | Cons(hd, tl) ->
      (match p hd with
       | true -> Cons(hd, filter p tl)
       | false -> filter p tl)
  let rec foldr f acc = function
    | Nil -> acc
    | Cons(hd, tl) -> f hd (foldr f acc tl)
  let rec foldl f acc = function
    | Nil -> acc
    | Cons(hd, tl) -> foldl f (f acc hd) tl
end

open Linkedlist
