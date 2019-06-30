open Sequence
open Unittest

module SeqTest (S : Sequence) = struct
  open S
  let print_seq_name s = Printf.printf "Tests from %s: \n" s
  let tests = [mk_standard_test "is_empty_test_true" (fun() -> is_empty (from_list [])) true;
               mk_standard_test "is_empty_test_false" (fun() -> is_empty (from_list [1;3])) false;
               (*mk_standard_test "length_of_empty_list" (fun() -> length (from_list [])) 0;
               mk_standard_test "length_of_list1" (fun() -> length (from_list [1;2])) 2;
               mk_standard_test "length_of_list2" (fun() -> length (from_list [1;2;3])) 3;
                 mk_standard_test "length_of_list3" (fun() -> length (from_list [1;2;3;4])) 4;*)
               mk_standard_test "first_of_one_element_list" (fun() -> first (from_list [1])) 1;
               mk_standard_test "first_of_list" (fun() -> first (from_list [1;3])) 1;
               (*mk_standard_test "last_of_one_element_list" (fun() -> last (from_list [3])) 3;
               mk_standard_test "last_of_list" (fun() -> last (from_list [1;3])) 3;
               mk_standard_test "get_nth_second" (fun() -> (nth (from_list [1;3])) 2) 3;
               mk_standard_test "to_list" (fun() -> (to_list (from_list [1;2]))) [1;2];
               mk_standard_test "push_to_empty_list" (fun() -> (to_list (push (from_list []) 1))) [1];
               mk_standard_test "push_to_list" (fun() -> (to_list (push (from_list [1;2]) 3))) [3;1;2];
               mk_standard_test "pop_list" (fun() -> (to_list (pop (from_list [1;2;3])))) [2;3];
               mk_standard_test "append_empty_list" (fun() -> (to_list (append (from_list [1;2]) (from_list [])))) [1;2];
               mk_standard_test "append_list" (fun() -> (to_list (append (from_list [1;2]) (from_list [3;4])))) [1;2;3;4];
               mk_standard_test "push_last_to_empty_list" (fun() -> (to_list (push_last (from_list []) 1))) [1];
               mk_standard_test "push_last_to_list" (fun() -> (to_list (push_last (from_list [1;2]) 3))) [1;2;3];
               mk_standard_test "pop_last_from_list" (fun() -> (to_list (pop_last (from_list [1;2])))) [1];
               mk_standard_test "take_zero_from_list" (fun() -> (to_list (take (from_list [1;2;3]) 0))) [];
               mk_standard_test "take_two_from_list" (fun() -> (to_list (take (from_list [1;2;3]) 2))) [1;2];
               mk_standard_test "drop_zero_from_list" (fun() -> (to_list (drop (from_list [1;2]) 0))) [1;2];
               mk_standard_test "drop_zero_from_empty_list" (fun() -> (to_list (drop (from_list []) 0))) [];
               mk_standard_test "drop_two_from_list" (fun() -> (to_list (drop (from_list [1;2;3]) 2))) [3];
               mk_standard_test "foldr_minus" (fun() -> (foldr (fun x y -> x - y) 100 (from_list [4;1;2;3]))) 102;
               mk_standard_test "foldl_minus" (fun() -> (foldl (fun x y -> x - y) 100 (from_list [1;2;3]))) 94;
               mk_standard_test "foldr_add_div" (fun() -> (foldr (fun x y -> (x + y) / 2) 100 (from_list [100; 200]))) 125;
               mk_standard_test "foldl_add_div" (fun() -> (foldl (fun x y -> (x + y) / 2) 100 (from_list [100; 200]))) 150;
               mk_standard_test "foldr_string" (fun() -> (foldr (fun x y -> x ^ y) "a" (from_list ["b";"c";"d"]))) "bcda";
               mk_standard_test "foldl_string" (fun() -> (foldl (fun x y -> x ^ y) "a" (from_list ["b";"c";"d"]))) "abcd";
               mk_standard_test "filter_smaller_than_two" (fun() -> (to_list (filter (fun x -> x < 2) (from_list [1;2;3])))) [1];
               mk_standard_test "find_smaller_than_two" (fun() -> (find (fun x -> x < 2) (from_list [2;1;3]))) (Some 1);
               mk_standard_test "find_smaller_than_two" (fun() -> (find (fun x -> x < 2) (from_list [2;3;3]))) (None);
               mk_standard_test "all_false" (fun() -> (all (fun x -> x < 2) (from_list [2;1;3]))) false;
               mk_standard_test "all_true" (fun() -> (all (fun x -> x < 4) (from_list [2;1;3]))) true;
               mk_standard_test "any_false" (fun() -> (any (fun x -> x < 2) (from_list [2;3;4]))) false;
               mk_standard_test "any_true" (fun() -> (any (fun x -> x < 2) (from_list [2;1;4]))) true;
               mk_standard_test "map_add_int" (fun() -> (to_list (map (fun x -> x + 2) (from_list [1;2;3])))) [3;4;5];
                 mk_standard_test "map_conc_string" (fun() -> (to_list (map (fun x -> x ^ "!") (from_list ["hello";"no"])))) ["hello!";"no!"];*)
              ]
  let _ = print_seq_name get_seq_name
  let _ = run_tests tests
end
