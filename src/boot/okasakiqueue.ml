open Sequence
open Fingertree

exception Empty
exception IndexOutOfBounds

module Okasakiqueue : Sequence = struct
  (* Constructors *)
  type 'a queue =
    | QueueCons of 'a Fingertree.sequence * 'a Fingertree.sequence

  type 'a sequence = 'a queue

  let get_seq_name = "Okasaki Queue"

  (*WC: O(N)*)
  let check_f = function
    | QueueCons(f, r) ->
      if (Fingertree.is_empty f) then
        QueueCons(Fingertree.reverse r, Fingertree.empty)
      else
        QueueCons(f, r)

  (*WC: O(N)*)
  let rec from_list l =
    let r = Fingertree.reverse (Fingertree.from_list l) in (*O(N) + O(N)*)
    let f = Fingertree.empty in (*O(1)*)
    check_f (QueueCons(f,r)) (*O(N)*)
  (*WC: O(N)*)
  let rec to_list q =
    match check_f q with
    | QueueCons(f, r) ->
      Fingertree.to_list (Fingertree.append f (Fingertree.reverse r)) (*O(N) + O(N/2) + O(N)*)

  (*WC: O(1)*)
  let empty = QueueCons(Fingertree.empty, Fingertree.empty) (*O(1)*)
  (*WC: O(1)*)
  let is_empty = function
    | QueueCons(f, _) ->
      if Fingertree.is_empty f then
        true
      else
        false
  (*WC: O(1)*)
  let first = function
    | QueueCons(f, _) ->
      Fingertree.first f (*O(1)*)
  (*WC: O(N)*)
  let last = function
    | QueueCons(f, r) ->
      if (Fingertree.is_empty r) then
        Fingertree.last f (*O(N)*)
      else
        Fingertree.first r (*O(1)*)
  (*WC: O(1)*)
  let push q x = match q with
    | QueueCons(f, r) ->
      let f2 = Fingertree.push f x in (*O(1)*)
      QueueCons(f2, r)
  (*WC: O(N)*)
  let pop = function
    | QueueCons(f, r) ->
      let f2 = Fingertree.pop f in (*O(1)*)
      check_f (QueueCons(f2, r)) (*O(N-1)*)
  (*WC: O(N)*)
  let length = function
    | QueueCons(f, r) ->
      Fingertree.length f + Fingertree.length r (*O(N/2) + O(N/2)*)
  (*WC: O(N)*)
  let nth q n = match q with
    | QueueCons(f, r) ->
      if Fingertree.length f > n then
        Fingertree.nth f n (*O(n)*)
      else
        Fingertree.nth r ((Fingertree.length r) + 1 - (n - (Fingertree.length f))) (*O((n-f))*)
  (*WC: O(N)*)
  let append q1 q2 =
    match (q1, q2) with
    | (QueueCons(f1, r1), QueueCons(f2, r2)) ->
      let rev_f2 = Fingertree.reverse f2 in (*O(N/4)*)
      let r3 = Fingertree.append r2 rev_f2 in (*O(N/4)*)
      let r4 = Fingertree.append r3 r1 in (*O(N/2)*)
      check_f (QueueCons(f1, r4)) (*O(N)*)
  (*WC: O(N)*)
  let reverse = function
    | QueueCons(f,r) -> check_f (QueueCons(r, f))
  (*WC: O(N)*)
  let push_last q x = match q with
    | QueueCons(f, r) ->
      let r2 = Fingertree.push r x in (*O(1)*)
      check_f (QueueCons(f, r2)) (*O(N)*) (*???*) (*Om det alltid stämmer, så är det bara om listan är helt tom, och då O(1)*)
  (*WC: O(N)*)
  let pop_last = function
    | QueueCons(f, r) ->
      if Fingertree.is_empty r then (*O(1)*)
        let f2 = Fingertree.pop_last f in (*O(N)*)
        QueueCons(f2, r)
      else
        let r2 = Fingertree.pop r in (*O(1)*)
        QueueCons(f, r2)
  (*O(N)*)
  let take q n = match q with
    | QueueCons(f, r) ->
      if n > length q then (*O(N)*)
        raise IndexOutOfBounds
      else if n <= Fingertree.length f then
        let f2 = Fingertree.take f n in (*O(n) - allt kan ligga här*)
        (QueueCons(f2, Fingertree.empty))
      else
        let n2 = n - Fingertree.length f in
        let n3 = Fingertree.length r - n2 in
        let r2 = Fingertree.drop r n3 in (*O(n3) - allt kan ligga här*)
        QueueCons(f, r2)
  (*WC: O(N)*)
  let drop q n = match q with
    | QueueCons(f, r) ->
      if n > length q then (*O(N)*)
        raise IndexOutOfBounds
      else if n <= Fingertree.length f then
        let f2 = Fingertree.drop f n in (*O(n)*)
        check_f (QueueCons(f2, r)) (*O(N-n)*)
      else
        let n2 = n - Fingertree.length f in (*O(N)*)
        let n3 = Fingertree.length r - n2 in (*O(N)*)
        let r2 = Fingertree.take r n3 in (*O(n3)*)
        check_f (QueueCons(Fingertree.empty, r2)) (*O(N)*)
  (*WC: O(N)*)
  let map fn = function
    | QueueCons(f, r) ->
      let f2 = Fingertree.map fn f in (*O(N/2)*)
      let r2 = Fingertree.map fn r in (*O(N/2)*)
      QueueCons(f2, r2)
  (*WC: O(N)*)
  let any b = function
    | QueueCons(f, r) ->
      Fingertree.any b f || Fingertree.any b r
  (*WC:O(N)*)
  let all b = function
    | QueueCons(f, r) ->
      if Fingertree.is_empty r then
        Fingertree.all b f
      else
        Fingertree.all b f
  (*WC: O(N)*)
  let find p = function
    | QueueCons(f, r) ->
      let ll = Fingertree.append f r in
      Fingertree.find p ll
  (*WC: O(N)*)
  let filter p = function
    | QueueCons(f, r) ->
      let f2 = Fingertree.filter p f in
      let r2 = Fingertree.filter p r in
      check_f (QueueCons(f2, r2))
  (*WC: O(N)*)
  let foldr fn acc = function
    | QueueCons(f, r) ->
      let rev_r = Fingertree.reverse r in
      let l = Fingertree.append f rev_r in
      Fingertree.foldr fn acc l
  (*WC: O(N)*)
  let foldl fn acc = function
    | QueueCons(f, r) ->
      let rev_r = Fingertree.reverse r in
      let l = Fingertree.append f rev_r in
      Fingertree.foldl fn acc l
  (*WC: O(1)*)
  let copy q =
    q
end

open Okasakiqueue
