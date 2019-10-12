open Sequence
open Linkedlist
(*open Test*)
(*open Unittest*)

exception Empty
exception IndexOutOfBounds

module Queue : Sequence = struct
  (* Constructors *)
  type 'a queue =
    | QueueCons of 'a Linkedlist.sequence * 'a Linkedlist.sequence

  type 'a sequence = 'a queue

  let get_seq_name = "Queue"

  let check_f = function
    | QueueCons(f, r) ->
      if (Linkedlist.is_empty f) then
        QueueCons(Linkedlist.reverse r, Linkedlist.empty)
      else
        QueueCons(f, r)
  let rec from_list_helper r l = match l with
    | [] -> r
    | hd::tl ->
      let r2 = Linkedlist.push r hd in
      from_list_helper r2 tl

  let rec from_list l =
    let r_from_list = from_list_helper Linkedlist.empty l in
    check_f (QueueCons(Linkedlist.empty, r_from_list))
  let rec to_list = function
    | QueueCons(f, r) ->
      if Linkedlist.is_empty f && Linkedlist.is_empty r then
        []
      else if Linkedlist.is_empty f then
        to_list (check_f (QueueCons(f,r)))
      else
        Linkedlist.first f :: to_list (QueueCons (Linkedlist.drop f 1, r))

  let empty = QueueCons(Linkedlist.empty, Linkedlist.empty)
  let is_empty = function
    | QueueCons(f, _) ->
      if Linkedlist.is_empty f then
        true
      else
        false
  let first = function
    | QueueCons(f, _) ->
      if Linkedlist.is_empty f then
        raise Empty
      else
        Linkedlist.first f
  let last = function
    | QueueCons(f, r) ->
      if Linkedlist.is_empty f then
        raise Empty
      else if Linkedlist.is_empty r then
        Linkedlist.last f
      else
        Linkedlist.first r
  let push q x = match q with
    | QueueCons(f, r) ->
      let f2 = Linkedlist.push f x in
      QueueCons(f2, r)
  let pop = function
    | QueueCons(f, r) ->
      let f2 = Linkedlist.pop f in
      check_f (QueueCons(f2, r))
  let length = function
    | QueueCons(f, r) ->
      Linkedlist.length f + Linkedlist.length r
  let nth q n = match q with
    | QueueCons(f, r) ->
      if Linkedlist.length f <= n then
        Linkedlist.nth f n
      else
        Linkedlist.nth r ((Linkedlist.length r) + 1 - (n - (Linkedlist.length f)))
  let append q1 q2 = match (q1, q2) with
    | (QueueCons(f1, r1), QueueCons(f2, r2)) ->
      let rev_f2 = Linkedlist.reverse f2 in
      let r3 = Linkedlist.append r2 rev_f2 in
      let r4 = Linkedlist.append r3 r1 in
      check_f (QueueCons(f1, r4))
  let reverse = function
    | QueueCons(f,r) -> check_f (QueueCons(r, f))
  let push_last q x = match q with
    | QueueCons(f, r) ->
      let r2 = Linkedlist.push r x in
      check_f (QueueCons(f, r2))
  let pop_last = function
    | QueueCons(f, r) ->
      if Linkedlist.is_empty r then
        let f2 = Linkedlist.pop_last f in
        QueueCons(f2, r)
      else
        let r2 = Linkedlist.pop r in
        QueueCons(f, r2)
  let take q n = match q with
    | QueueCons(f, r) ->
      if n > length q then
        raise IndexOutOfBounds
      else if n <= Linkedlist.length f then
        let f2 = Linkedlist.take f n in
        (QueueCons(f2, Linkedlist.empty))
      else
        let n2 = n - Linkedlist.length f in
        let n3 = Linkedlist.length r - n2 in
        let r2 = Linkedlist.drop r n3 in
        QueueCons(f, r2)
  let drop q n = match q with
    | QueueCons(f, r) ->
      if n > length q then
        raise IndexOutOfBounds
      else if n <= Linkedlist.length f then
        let f2 = Linkedlist.drop f n in
        check_f (QueueCons(f2, r))
      else
        let n2 = n - Linkedlist.length f in
        let n3 = Linkedlist.length r - n2 in
        let r2 = Linkedlist.take r n3 in
        check_f (QueueCons(Linkedlist.empty, r2))

  let map fn = function
    | QueueCons(f, r) ->
      let f2 = Linkedlist.map fn f in
      let r2 = Linkedlist.map fn r in
      QueueCons(f2, r2)
  let any b = function
    | QueueCons(f, r) ->
      Linkedlist.any b f || Linkedlist.any b r
  let all b = function
    | QueueCons(f, r) ->
      Linkedlist.all b f && Linkedlist.all b r
  let find p = function
    | QueueCons(f, r) ->
      let ll = Linkedlist.append f r in
      Linkedlist.find p ll
  let filter p = function
    | QueueCons(f, r) ->
      let f2 = Linkedlist.filter p f in
      let r2 = Linkedlist.filter p r in
      check_f (QueueCons(f2, r2))
  let foldr fn acc = function
    | QueueCons(f, r) ->
      let rev_r = Linkedlist.reverse r in
      let l = Linkedlist.append f rev_r in
      Linkedlist.foldr fn acc l
  let foldl fn acc = function
    | QueueCons(f, r) ->
      let rev_r = Linkedlist.reverse r in
      let l = Linkedlist.append f rev_r in
      Linkedlist.foldl fn acc l
end

open Queue
