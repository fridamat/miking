open Sequence
open Fingertree
(*open Test*)
(*open Unittest*)

exception Empty
exception IndexOutOfBounds

module Queue : Sequence = struct
  (* Constructors *)
  type 'a queue =
    | QueueCons of 'a Fingertree.sequence * 'a Fingertree.sequence

  type 'a sequence = 'a queue

  let get_seq_name = "Queue"

  let check_f = function
    | QueueCons(f, r) ->
      if (Fingertree.is_empty f) then
        QueueCons(Fingertree.reverse r, Fingertree.empty)
      else
        QueueCons(f, r)
  let rec from_list_helper r l = match l with
    | [] -> r
    | hd::tl ->
      let r2 = Fingertree.push r hd in
      from_list_helper r2 tl

  let rec from_list l =
    let r_from_list = from_list_helper Fingertree.empty l in
    check_f (QueueCons(Fingertree.empty, r_from_list))
  let rec to_list = function
    | QueueCons(f, r) ->
      if Fingertree.is_empty f && Fingertree.is_empty r then
        []
      else if Fingertree.is_empty f then
        to_list (check_f (QueueCons(f,r)))
      else
        Fingertree.first f :: to_list (QueueCons (Fingertree.drop f 1, r))

  let empty = QueueCons(Fingertree.empty, Fingertree.empty)
  let is_empty = function
    | QueueCons(f, _) ->
      if Fingertree.is_empty f then
        true
      else
        false
  let first = function
    | QueueCons(f, _) ->
      if Fingertree.is_empty f then
        raise Empty
      else
        Fingertree.first f
  let last = function
    | QueueCons(f, r) ->
      if Fingertree.is_empty f then
        raise Empty
      else if Fingertree.is_empty r then
        Fingertree.last f
      else
        Fingertree.first r
  let push q x = match q with
    | QueueCons(f, r) ->
      let f2 = Fingertree.push f x in
      QueueCons(f2, r)
  let pop = function
    | QueueCons(f, r) ->
      let f2 = Fingertree.pop f in
      check_f (QueueCons(f2, r))
  let length = function
    | QueueCons(f, r) ->
      Fingertree.length f + Fingertree.length r
  let nth q n = match q with
    | QueueCons(f, r) ->
      if Fingertree.length f <= n then
        Fingertree.nth f n
      else
        Fingertree.nth r ((Fingertree.length r) + 1 - (n - (Fingertree.length f)))
  let append q1 q2 = match (q1, q2) with
    | (QueueCons(f1, r1), QueueCons(f2, r2)) ->
      let rev_f2 = Fingertree.reverse f2 in
      let r3 = Fingertree.append r2 rev_f2 in
      let r4 = Fingertree.append r3 r1 in
      check_f (QueueCons(f1, r4))
  let reverse = function
    | QueueCons(f,r) -> check_f (QueueCons(r, f))
  let push_last q x = match q with
    | QueueCons(f, r) ->
      let r2 = Fingertree.push r x in
      check_f (QueueCons(f, r2))
  let pop_last = function
    | QueueCons(f, r) ->
      if Fingertree.is_empty r then
        let f2 = Fingertree.pop_last f in
        QueueCons(f2, r)
      else
        let r2 = Fingertree.pop r in
        QueueCons(f, r2)
  let take q n = match q with
    | QueueCons(f, r) ->
      if n > length q then
        raise IndexOutOfBounds
      else if n <= Fingertree.length f then
        let f2 = Fingertree.take f n in
        (QueueCons(f2, Fingertree.empty))
      else
        let n2 = n - Fingertree.length f in
        let n3 = Fingertree.length r - n2 in
        let r2 = Fingertree.drop r n3 in
        QueueCons(f, r2)
  let drop q n = match q with
    | QueueCons(f, r) ->
      if n > length q then
        raise IndexOutOfBounds
      else if n <= Fingertree.length f then
        let f2 = Fingertree.drop f n in
        check_f (QueueCons(f2, r))
      else
        let n2 = n - Fingertree.length f in
        let n3 = Fingertree.length r - n2 in
        let r2 = Fingertree.take r n3 in
        check_f (QueueCons(Fingertree.empty, r2))

  let map fn = function
    | QueueCons(f, r) ->
      let f2 = Fingertree.map fn f in
      let r2 = Fingertree.map fn r in
      QueueCons(f2, r2)
  let any b = function
    | QueueCons(f, r) ->
      Fingertree.any b f || Fingertree.any b r
  let all b = function
    | QueueCons(f, r) ->
      Fingertree.all b f && Fingertree.all b r
  let find p = function
    | QueueCons(f, r) ->
      let ll = Fingertree.append f r in
      Fingertree.find p ll
  let filter p = function
    | QueueCons(f, r) ->
      let f2 = Fingertree.filter p f in
      let r2 = Fingertree.filter p r in
      check_f (QueueCons(f2, r2))
  let foldr fn acc = function
    | QueueCons(f, r) ->
      let rev_r = Fingertree.reverse r in
      let l = Fingertree.append f rev_r in
      Fingertree.foldr fn acc l
  let foldl fn acc = function
    | QueueCons(f, r) ->
      let rev_r = Fingertree.reverse r in
      let l = Fingertree.append f rev_r in
      Fingertree.foldl fn acc l
  let equals l1 l2 =
    match l1, l2 with
    | QueueCons(f1, r1), QueueCons(f2, r2) ->
      (Fingertree.equals f1 f2) && (Fingertree.equals r1 r2)
end

open Queue
