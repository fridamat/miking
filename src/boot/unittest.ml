type test =
    Test : string * ('a -> 'a -> bool) * (unit -> 'a) * 'a -> test
type test_result =
  | TestSuccess of string
  | TestFail of string

let mk_test id cmp t v = Test (id, cmp, t, v)
let mk_standard_test id = mk_test id (fun x y -> x = y)

let run_test = function
  | Test(id, cmp, t, v) ->
    if cmp (t ()) v
    then TestSuccess id
    else TestFail id

let is_failed = function
  | TestSuccess _ -> false
  | TestFail _ -> true
let print_result = function
  | TestSuccess id -> Printf.printf "Test \"%s\" passed\n" id
  | TestFail id -> Printf.printf "Test \"%s\"failed\n" id
let run_tests l =
  let results = List.map run_test l in
  let failed = List.filter is_failed results in
  let no_results = List.length results in
  let no_failed = List.length failed in
  if no_failed == 0 then
    Printf.printf "All tests passed\n"
  else
    Printf.printf "%d/%d tests passed.\n" (no_results - no_failed) no_results;
    List.iter print_result failed

(*
  let tests = [mk_test (fun x y -> x == y) (fun () -> length [1,2,3]) 3, ...]
*)
