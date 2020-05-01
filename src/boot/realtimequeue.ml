open Sequence
open Fingertree
open Stream

exception Empty1
exception Empty2
exception Empty3
exception IndexOutOfBounds
exception NotImplemented

module Realtimequeue : Sequence = struct
  (* Constructors *)
  type 'a realtimequeue =
    | RTQCons of 'a Stream.sequence * 'a Fingertree.sequence * 'a Stream.sequence

  type 'a sequence = 'a realtimequeue

  let rec rotate rtq =
    match rtq with
    | RTQCons(s1, l, s2) ->
      if Stream.is_empty s1 then
        Stream.push s2 (Fingertree.first l)
      else
        Stream.push (rotate (RTQCons((Stream.drop s1 1), (Fingertree.drop l 1), (Stream.push s2 (Fingertree.first l))))) (Stream.first s1)
  let exec rtq =
    match rtq with
    | RTQCons(s1, l, s2) ->
      if Stream.is_empty s2 then
        let s3 = (rotate rtq) in RTQCons(s3, (Fingertree.empty), s3)
      else
        RTQCons(s1, l, (Stream.drop s2 1))

  let get_seq_name = "Real Time Queue"

  let from_list = function
    | [] -> RTQCons(Stream.empty, Fingertree.empty, Stream.empty)
    | l -> exec (RTQCons(Stream.empty, (Fingertree.from_list l), Stream.empty))
  let to_list rtq =
    match rtq with
    | RTQCons(s1, l, s2) ->
      if Stream.is_empty s1 then
        []
      else
        List.append (Stream.to_list s1) (Fingertree.to_list (Fingertree.reverse l))


  let empty = RTQCons(Stream.empty, Fingertree.empty, Stream.empty)
  let is_empty rtq =
    match rtq with
    | RTQCons(s1, _, _) ->
      if Stream.is_empty s1 then
        true
      else
        false
  let first rtq =
    match rtq with
    | RTQCons(s1, _, _) ->
      if Stream.is_empty s1 then
        raise Empty1
      else
        Stream.first s1
  let last rtq =
    match rtq with
    | RTQCons(s1, l, s2) ->
      if Fingertree.is_empty l then
        raise Empty2
      else
        Fingertree.first l
  let push rtq x =
    match rtq with
    | RTQCons(s1, l, s2) -> exec (RTQCons(s1, (Fingertree.push l x), s2))
  let pop rtq = rtq (*TODO*)
  let length rtq =
    match rtq with
    | RTQCons(s1, l, s2) -> (Stream.length s1) + (Fingertree.length l)
  let nth rtq n =
    match rtq with
    | RTQCons(s1, l, s2) ->
      if Fingertree.is_empty l then
        raise Empty3
      else
        Fingertree.first l (*TODO*)
  let append rtq1 rtq2 = rtq1 (*TODO*)
  let reverse rtq = rtq (*TODO*)
  let push_last rtq x = rtq (*TODO*)
  let pop_last rtq = rtq (*TODO*)
  let take rtq n = rtq (*TODO*)
  let drop rtq n = rtq (*TODO*)

  let map f rtq =
    match rtq with
    | RTQCons(s1, l, s2) ->
      let f1 = Fingertree.map f l in RTQCons(Stream.empty, f1, Stream.empty)
  let any p rtq =
    match rtq with
    | RTQCons(s1, l, s2) ->
      p (Fingertree.first l) (*TODO*)
  let all p rtq =
    match rtq with
    | RTQCons(s1, l, s2) ->
      p (Fingertree.first l) (*TODO*)
  let find p rtq =
    match rtq with
    | RTQCons(s1, l, s2) ->
      Fingertree.find p l (*TODO*)
  let filter p rtq = rtq (*TODO*)
  let foldr f x rtq = x (*TODO*)
  let foldl f x rtq = x (*TODO*)
  let equals rtq1 rtq2 = true (*TODO*)
end

open Realtimequeue
