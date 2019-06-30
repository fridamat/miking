type test
val mk_test : string -> ('a -> 'a -> bool) -> (unit -> 'a) -> 'a -> test
val mk_standard_test : string -> (unit -> 'a) -> 'a -> test
val run_tests : test list -> unit
