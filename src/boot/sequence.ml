module type Sequence = sig
  type 'a sequence

  val get_seq_name : string

  val from_list : 'a list -> 'a sequence
  val to_list : 'a sequence -> 'a list

  val empty : 'a sequence
  val is_empty : 'a sequence -> bool
  val first : 'a sequence -> 'a
  val last : 'a sequence -> 'a
  val push : 'a sequence -> 'a -> 'a sequence (* Add element to beginning of sequence *)
  val pop : 'a sequence -> 'a sequence (* Remove first element in sequence *)
  val length : 'a sequence -> int
  val nth : 'a sequence -> int -> 'a (* Get the nth element in the sequence *)
  val append : 'a sequence -> 'a sequence -> 'a sequence
  val reverse : 'a sequence -> 'a sequence
  val push_last : 'a sequence -> 'a -> 'a sequence (* Add element to end of sequence *)
  val pop_last : 'a sequence -> 'a sequence (* Remove last element in sequence *)
  val take : 'a sequence -> int -> 'a sequence (* Get the n first elements of the sequence *)
  val drop : 'a sequence -> int -> 'a sequence (* Remove the n first elements of the sequence *)

  val map : ('a -> 'b) -> 'a sequence -> 'b sequence
  val any : ('a -> bool) -> 'a sequence -> bool
  val all : ('a -> bool) -> 'a sequence -> bool
  val find : ('a -> bool) -> 'a sequence -> 'a
  val filter : ('a -> bool) -> 'a sequence -> 'a sequence
  val foldr : ('a -> 'b -> 'b) -> 'b -> 'a sequence -> 'b
  val foldl : ('b -> 'a -> 'b) -> 'b -> 'a sequence -> 'b

  val copy : 'a sequence -> 'a sequence
end
