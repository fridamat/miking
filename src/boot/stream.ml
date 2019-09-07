open Sequence

exception Empty
exception IndexOutOfBounds
exception NotFound
exception NotImplemented

module Stream : Sequence = struct
  (* SConstructors *)
  type 'a stream_cell =
    | Nil
    | SCons of 'a * 'a stream
  and 'a stream = 'a stream_cell Lazy.t

  type 'a sequence = 'a stream

  let rec reverse_helper s rev_s =
    match s with
    | lazy Nil -> rev_s
    | lazy (SCons(hd, tl)) -> reverse_helper tl (SCons(hd, (lazy rev_s)))

  let get_seq_name = "Stream"

  let rec from_list = function
    | [] -> lazy Nil
    | hd::tl -> lazy (SCons(hd, from_list tl))
  let rec to_list = function
    | lazy Nil -> []
    | lazy(SCons(hd, tl)) -> hd::(to_list tl)

  let empty = lazy Nil
  let is_empty s =
    match s with
    | lazy Nil -> true
    | _ -> false
  let first s =
    match s with
    | lazy Nil -> raise Empty
    | lazy (SCons(hd, _)) -> hd
  let rec last s =
    match s with
    | lazy Nil -> raise Empty
    | lazy (SCons(hd, lazy Nil)) -> hd
    | lazy (SCons(hd, tl)) -> last tl
  let push s x = lazy (SCons(x, s)) (*Should it be SCons(x, lazy s)???*)
  let pop s =
    match s with
    | lazy Nil -> raise Empty
    | lazy (SCons(hd, tl)) -> tl
  let rec length s =
    match s with
    | lazy Nil -> 0
    | lazy (SCons(_, tl)) -> 1 + (length tl)
  let rec nth s n =
    match s, n with
    | lazy Nil, _ -> raise IndexOutOfBounds
    | lazy (SCons(hd, _)), 1 -> hd
    | lazy (SCons(_, tl)), _ -> nth tl (n-1)
  let rec append s1 s2 = lazy (
    match s1 with
    | lazy Nil -> Lazy.force s2
    | lazy (SCons(hd, tl)) -> SCons(hd, (append tl s2))
  )
  let reverse s = lazy (
    reverse_helper s Nil
  )
  let rec push_last s x = lazy (
    match s with
    | lazy Nil -> SCons(x, lazy Nil)
    | lazy (SCons(hd, tl)) -> SCons(hd, (push_last tl x))
  )
  let rec pop_last s = lazy (
    match s with
    | lazy Nil -> raise Empty
    | lazy (SCons(hd, lazy Nil)) -> Nil
    | lazy (SCons(hd, tl)) -> SCons(hd, (pop_last tl))
  )
  let rec take s n = lazy (
    match s, n with
    | _, 0 -> Nil
    | lazy Nil, _ -> Nil (*In linked list this gives an error*)
    | lazy (SCons(hd, tl)), _ -> SCons(hd, (take tl (n-1)))
  )
  let rec drop s n = lazy (
    match s, n with
    | _, 0 -> Lazy.force s
    | lazy Nil, _ -> Nil
    | lazy (SCons(hd, tl)), _ -> Lazy.force (drop tl (n-1))
  )

  let rec map f s = lazy (
    match s with
    | lazy Nil -> Nil
    | lazy (SCons(hd, tl)) -> SCons((f hd), (map f tl))
  )
  let rec any p s =
    match s with
    | lazy Nil -> false
    | lazy (SCons(hd, tl)) -> p hd || any p tl
  let rec all p s =
    match s with
    | lazy Nil -> true
    | lazy (SCons(hd, tl)) -> p hd && all p tl
  let rec find p s =
    match s with
    | lazy Nil -> raise NotFound
    | lazy (SCons(hd, tl)) ->
      (match p hd with
       | true -> hd
       | false -> find p tl)
  let rec filter p s = lazy (
    match s with
    | lazy Nil -> Nil
    | lazy (SCons(hd, tl)) ->
      (match p hd with
       | true -> SCons(hd, filter p tl)
       | false -> Lazy.force (filter p tl))
  )
  let rec foldr f acc s =
    match s with
    | lazy Nil -> acc
    | lazy (SCons(hd, tl)) -> f hd (foldr f acc tl)
  let rec foldl f acc s =
    match s with
    | lazy Nil -> acc
    | lazy (SCons(hd, tl)) -> foldl f (f acc hd) tl
  let rec equals s1 s2 =
    match s1, s2 with
    | lazy Nil, lazy Nil -> true
    | lazy Nil, _ | _, lazy Nil -> false
    | lazy (SCons(hd1,tl1)), lazy (SCons(hd2,tl2)) ->
      if hd1 == hd2 then
        equals tl1 tl2
      else
        false
end

open Stream
