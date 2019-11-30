open Sequence
open Linkedlist

exception Empty
exception IndexOutOfBounds

module Okasakiqueue : Sequence = struct
  (* Constructors *)
  type 'a queue =
    | QueueCons of 'a Linkedlist.sequence * 'a Linkedlist.sequence

  type 'a sequence = 'a queue

  let get_seq_name = "Okasaki Queue"

  (*WC: O(N)*)
  let check_f = function
    | QueueCons(f, r) ->
      if (Linkedlist.is_empty f) then
        QueueCons(Linkedlist.reverse r, Linkedlist.empty)
      else
        QueueCons(f, r)

  (*WC: O(N)*)
  let rec from_list l =
    let r = Linkedlist.reverse (Linkedlist.from_list l) in (*O(N) + O(N)*)
    let f = Linkedlist.empty in (*O(1)*)
    check_f (QueueCons(f,r)) (*O(N)*)
  (*WC: O(N)*)
  let rec to_list q =
    match check_f q with
    | QueueCons(f, r) ->
      Linkedlist.to_list (Linkedlist.append f (Linkedlist.reverse r)) (*O(N) + O(N/2) + O(N)*)

  (*WC: O(1)*)
  let empty = QueueCons(Linkedlist.empty, Linkedlist.empty) (*O(1)*)
  (*WC: O(1)*)
  let is_empty = function
    | QueueCons(f, _) ->
      if Linkedlist.is_empty f then
        true
      else
        false
  (*WC: O(1)*)
  let first = function
    | QueueCons(f, _) ->
      Linkedlist.first f (*O(1)*)
  (*WC: O(N)*)
  let last = function
    | QueueCons(f, r) ->
      if (Linkedlist.is_empty r) then
        Linkedlist.last f (*O(N)*)
      else
        Linkedlist.first r (*O(1)*)
  (*WC: O(1)*)
  let push q x = match q with
    | QueueCons(f, r) ->
      let f2 = Linkedlist.push f x in (*O(1)*)
      QueueCons(f2, r)
  (*WC: O(N)*)
  let pop = function
    | QueueCons(f, r) ->
      let f2 = Linkedlist.pop f in (*O(1)*)
      check_f (QueueCons(f2, r)) (*O(N-1)*)
  (*WC: O(N)*)
  let length = function
    | QueueCons(f, r) ->
      Linkedlist.length f + Linkedlist.length r (*O(N/2) + O(N/2)*)
  (*WC: O(N)*)
  let nth q n = match q with
    | QueueCons(f, r) ->
      if Linkedlist.length f > n then
        Linkedlist.nth f n (*O(n)*)
      else
        Linkedlist.nth r ((Linkedlist.length r) + 1 - (n - (Linkedlist.length f))) (*O((n-f))*)
  (*WC: O(N)*)
  let append q1 q2 =
    match (q1, q2) with
    | (QueueCons(f1, r1), QueueCons(f2, r2)) ->
      let rev_f2 = Linkedlist.reverse f2 in (*O(N/4)*)
      let r3 = Linkedlist.append r2 rev_f2 in (*O(N/4)*)
      let r4 = Linkedlist.append r3 r1 in (*O(N/2)*)
      check_f (QueueCons(f1, r4)) (*O(N)*)
  (*WC: O(N)*)
  let reverse = function
    | QueueCons(f,r) -> check_f (QueueCons(r, f))
  (*WC: O(N)*)
  let push_last q x = match q with
    | QueueCons(f, r) ->
      let r2 = Linkedlist.push r x in (*O(1)*)
      check_f (QueueCons(f, r2)) (*O(N)*) (*???*) (*Om det alltid stämmer, så är det bara om listan är helt tom, och då O(1)*)
  (*WC: O(N)*)
  let pop_last = function
    | QueueCons(f, r) ->
      if Linkedlist.is_empty r then (*O(1)*)
        let f2 = Linkedlist.pop_last f in (*O(N)*)
        QueueCons(f2, r)
      else
        let r2 = Linkedlist.pop r in (*O(1)*)
        QueueCons(f, r2)
  (*O(N)*)
  let take q n = match q with
    | QueueCons(f, r) ->
      if n > length q then (*O(N)*)
        raise IndexOutOfBounds
      else if n <= Linkedlist.length f then
        let f2 = Linkedlist.take f n in (*O(n) - allt kan ligga här*)
        (QueueCons(f2, Linkedlist.empty))
      else
        let n2 = n - Linkedlist.length f in
        let n3 = Linkedlist.length r - n2 in
        let r2 = Linkedlist.drop r n3 in (*O(n3) - allt kan ligga här*)
        QueueCons(f, r2)
  (*WC: O(N)*)
  let drop q n = match q with
    | QueueCons(f, r) ->
      if n > length q then (*O(N)*)
        raise IndexOutOfBounds
      else if n <= Linkedlist.length f then
        let f2 = Linkedlist.drop f n in (*O(n)*)
        check_f (QueueCons(f2, r)) (*O(N-n)*)
      else
        let n2 = n - Linkedlist.length f in (*O(N)*)
        let n3 = Linkedlist.length r - n2 in (*O(N)*)
        let r2 = Linkedlist.take r n3 in (*O(n3)*)
        check_f (QueueCons(Linkedlist.empty, r2)) (*O(N)*)
  (*WC: O(N)*)
  let map fn = function
    | QueueCons(f, r) ->
      let f2 = Linkedlist.map fn f in (*O(N/2)*)
      let r2 = Linkedlist.map fn r in (*O(N/2)*)
      QueueCons(f2, r2)
  (*WC: O(N)*)
  let any b = function
    | QueueCons(f, r) ->
      Linkedlist.any b f || Linkedlist.any b r
  (*WC:O(N)*)
  let all b = function
    | QueueCons(f, r) ->
      if Linkedlist.is_empty r then
        Linkedlist.all b f
      else
        Linkedlist.all b f
  (*WC: O(N)*)
  let find p = function
    | QueueCons(f, r) ->
      let ll = Linkedlist.append f r in
      Linkedlist.find p ll
  (*WC: O(N)*)
  let filter p = function
    | QueueCons(f, r) ->
      let f2 = Linkedlist.filter p f in
      let r2 = Linkedlist.filter p r in
      check_f (QueueCons(f2, r2))
  (*WC: O(N)*)
  let foldr fn acc = function
    | QueueCons(f, r) ->
      let rev_r = Linkedlist.reverse r in
      let l = Linkedlist.append f rev_r in
      Linkedlist.foldr fn acc l
  (*WC: O(N)*)
  let foldl fn acc = function
    | QueueCons(f, r) ->
      let rev_r = Linkedlist.reverse r in
      let l = Linkedlist.append f rev_r in
      Linkedlist.foldl fn acc l
  (*WC: O(1)*)
  let copy q =
    q
end

open Okasakiqueue
