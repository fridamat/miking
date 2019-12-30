open Complexities
open Costterms
open Frequencies
open Pervasives

exception UnknownComparisonResult
exception UnknownCostTerm
exception NoDataStructureOptions

module Dssa = struct
  (*--- Print methods ---*)

  (*WC: O(#costterms)*)
  let pair_to_string (a,b) =
    (Costterms.to_string a) ^ " with count " ^ (Pervasives.string_of_int b) ^ ", "

  (*WC: O(#elements in cost record * #cost terms)*)
  let rec get_cost_record_string cost_record =
    match cost_record with
    | [] -> "\n"
    | hd::tl ->
      (pair_to_string hd) ^ (get_cost_record_string tl)

  (*WC: O(#elements in cost record * #cost terms)*)
  let print_cost_record cost_record =
    Printf.printf "The cost record:\n%s" (get_cost_record_string cost_record)

  (*--- Helper methods ---*)

  (*WC: O(#number of elements in l)*)
  let rec add_to_end_of_list l e =
    match l with
    | [] -> e::[]
    | hd::tl -> hd::(add_to_end_of_list tl e)

  (*WC: O(#complexities)*)
  let compare_complexities complexity_1 complexity_2 =
    match Complexities.compare_complexities complexity_1 complexity_2 with (*WC: #complexities*)
    | 2 -> 2
    | 1 -> 1
    | 0 -> 0
    | -1 -> -1
    | -2 -> -2
    | _ -> raise UnknownComparisonResult

  (*WC: O(#frequencies)*)
  let compare_frequencies frequency_1 frequency_2 =
    match Frequencies.compare_frequencies frequency_1 frequency_2 with (*O(#frequencies)*)
    | 2 -> 2
    | 1 -> 1
    | 0 -> 0
    | -1 -> -1
    | -2 -> -2
    | _ -> raise UnknownComparisonResult

  (*WC: O(#complexities + #frequencies)*)
  let compare_cost_terms cost_term_1 cost_term_2 =
    let complexity_1 = Costterms.get_complexity cost_term_1 in (*WC: O(1)*)
    let complexity_2 = Costterms.get_complexity cost_term_2 in (*WC: O(1)*)
    let frequency_1 = Costterms.get_frequency cost_term_1 in (*WC: O(1)*)
    let frequency_2 = Costterms.get_frequency cost_term_2 in (*WC: O(1)*)
    match compare_complexities complexity_1 complexity_2 with (*WC: O(#complexities)*)
    | 2 -> 2
    | 1 -> 1
    | 0 -> (
        match compare_frequencies frequency_1 frequency_2 with (*WC: O(#frequencies)*)
        | 2 -> 2
        | 1 -> 1
        | 0 -> 0
        | -1 -> -1
        | -2 -> -2
        | _ -> raise UnknownComparisonResult)
    | -1 -> -1
    | -2 -> -2
    | _ -> raise UnknownComparisonResult

  (*WC: O(#complexities + #frequencies + #data structures)*)
  let get_new_best_max_cost_term_and_best_data_structures best_max_cost_term best_data_structures contender_cost_term contender_data_structure =
    match compare_cost_terms best_max_cost_term contender_cost_term with (*WC: O(#complexities + #frequencies)*)
    | 2 -> (best_max_cost_term, best_data_structures)
    | 1 -> (contender_cost_term, [contender_data_structure])
    | 0 -> (best_max_cost_term, (add_to_end_of_list best_data_structures contender_data_structure)) (*WC: O(#data structures)*)
    | -1 -> (best_max_cost_term, best_data_structures)
    | -2 -> (contender_cost_term, [contender_data_structure])
    | _ -> raise UnknownComparisonResult

  (*WC: O(#complexities + #frequencies)*)
  let get_max_cost_term cost_term_1 cost_term_2 =
    match compare_cost_terms cost_term_1 cost_term_2 with (*WC: O(#complexities + #frequencies)*)
    | 2 -> cost_term_1
    | 1 -> cost_term_1
    | 0 -> cost_term_1
    | -1 -> cost_term_2
    | -2 -> cost_term_2
    | _ -> raise UnknownComparisonResult

  (*WC: recursive - O(#data structures^2)*)
  let rec get_data_structures_with_zero_count_for_cost_term cost_term data_structures costs =
    let frequency = Costterms.get_frequency cost_term in (*WC: O(1)*)
    match frequency with
    | Frequencies.Zero -> data_structures
    | _ ->
      (match data_structures with
       | [] -> []
       | ds_hd::ds_tl ->
         let curr_cost_record = List.nth costs ds_hd in (*WC: O(#data structures)*)
         let cost_term_count = List.assoc cost_term curr_cost_record in (*WC: O(#cost terms)*)
         if cost_term_count == 0 then
           ds_hd::(get_data_structures_with_zero_count_for_cost_term cost_term ds_tl costs) (*WC: Recursive call*)
         else
           get_data_structures_with_zero_count_for_cost_term cost_term ds_tl costs (*WC: Recursive call*)
      )

  (*WC: O(#data structures * (#data structures + #cost terms)) => O(#data structures^2)*)
  let rec get_data_structures_with_min_count_for_cost_term_helper cost_term data_structures costs min_count contenders =
    let frequency = Costterms.get_frequency cost_term in (*WC: O(1)*)
    match frequency with
    | Frequencies.Zero -> data_structures
    | _ ->
      (match data_structures with
       | [] -> contenders
       | ds_hd::ds_tl ->
         let curr_cost_record = List.nth costs ds_hd in (*WC: #data structures*)
         let cost_term_count = List.assoc cost_term curr_cost_record in (*WC: #cost terms*)
         if cost_term_count < min_count then
           let new_min_count = cost_term_count in
           let new_contenders = [ds_hd] in
           get_data_structures_with_min_count_for_cost_term_helper cost_term ds_tl costs new_min_count new_contenders (*WC: Recursive call*)
         else if cost_term_count == min_count then
           let updated_contenders = add_to_end_of_list contenders ds_hd in (*WC: O(#data structures)*)
           get_data_structures_with_min_count_for_cost_term_helper cost_term ds_tl costs min_count updated_contenders (*WC: Recursive call*)
         else
           get_data_structures_with_min_count_for_cost_term_helper cost_term ds_tl costs min_count contenders (*WC: Recursive call*)
      )

  (*WC: O(#data structures^2)*)
  let get_data_structures_with_min_count_for_cost_term cost_term data_structures costs =
    get_data_structures_with_min_count_for_cost_term_helper cost_term data_structures costs max_int [] (*WC: #data structures^2*)

  (*WC: O(#complexities + #frequencies)*)
  let get_next_lower_cost_term cost_term =
    let frequency = Costterms.get_frequency cost_term in (*WC: O(1)*)
    let complexity = Costterms.get_complexity cost_term in (*WC: O(1)*)
    let next_lower_frequency = Frequencies.get_next_lower_frequency frequency in (*WC: O(#frequencies)*)
    let next_lower_complexity = Complexities.get_next_lower_complexity complexity in (*WC: O(#complexities)*)
    match (next_lower_frequency, next_lower_complexity) with
    | (Frequencies.None, Complexities.None) -> Costterms.create_cost_term next_lower_complexity next_lower_frequency (*WC: O(1)*)
    | (Frequencies.None, _) -> Costterms.create_cost_term next_lower_complexity Frequencies.Many (*WC: O(1)*)
    | _ -> Costterms.create_cost_term complexity next_lower_frequency (*WC: O(1)*)

  (*WC: O(#data structures * (#data structures^2 + #complexities + #frequencies)) => O(#data structures^3)*)
  let rec get_top_data_structures curr_cost_term best_data_structures costs =
    match (curr_cost_term, best_data_structures) with
    | ((Complexities.None, Frequencies.None), _) -> best_data_structures
    | (_, []) -> raise NoDataStructureOptions
    | _ ->
      let contenders = get_data_structures_with_zero_count_for_cost_term curr_cost_term best_data_structures costs in (*WC: O(#data structures^2)*)
      let next_cost_term = get_next_lower_cost_term curr_cost_term in (*WC: O(#complexities + #frequencies)*)
      (match contenders with
       | [] ->
         let new_contenders = get_data_structures_with_min_count_for_cost_term curr_cost_term best_data_structures costs in (*WC: O(#data structures^2)*)
         get_top_data_structures next_cost_term new_contenders costs
       | _ ->
         get_top_data_structures next_cost_term contenders costs
      )

  (*WC: O(#cost terms)*)
  let increment_cost_term_count cost_record cost_term =
    if List.mem_assoc cost_term cost_record then (*WC: O(#cost terms)*)
      let curr_count = List.assoc cost_term cost_record in (*WC: O(#cost terms)*)
      let updated_record = List.remove_assoc cost_term cost_record in (*WC: O(#cost terms)*)
      add_to_end_of_list updated_record (cost_term, (curr_count+1)) (*WC: O#cost terms*)
    else
      raise UnknownCostTerm

  (*WC: O(#complexities)*)
  let rec combine_complexities_with_frequency frequency complexities =
    match complexities with
    | [] -> []
    | comp_hd::comp_tl -> (Costterms.create_cost_term comp_hd frequency)::(combine_complexities_with_frequency frequency comp_tl) (*WC: O(1)*)

  (*WC: O(#frequencies * #complexities)*)
  let rec build_cost_terms frequencies complexities =
    match frequencies with
    | [] -> []
    | freq_hd::freq_tl ->
      List.append (combine_complexities_with_frequency freq_hd complexities) (*WC: O(#complexities)*) (build_cost_terms freq_tl complexities)

  (*WC: O(#cost terms)*)
  let rec init_cost_record_helper cost_terms =
    match cost_terms with
    | [] -> []
    | ct_hd::ct_tl ->
      (ct_hd,0)::(init_cost_record_helper ct_tl) (*WC: O(1), recursive call*)

  (*WC: #complexities + #frequencies + #cost terms*)
  let init_cost_record =
    let cost_terms = build_cost_terms Frequencies.get_frequencies (*WC: O(#frequencies)*) Complexities.get_complexities (*WC: O(#complexities)*) in
    init_cost_record_helper cost_terms (*WC: O(#cost terms)*)

  (*WC: O(1)*)
  let init_cost_term = (Complexities.None, Frequencies.None) (*WC: O(1)*)

  (*--- Main methods ---*)

  (*WC: O(#methods * (#variables + complexities + frequencies + cost terms))*)
  let rec go_through_methods k mf_row_i mc_row_j max_cost_term cost_record =
    if k == (List.length mf_row_i) then (*WC: O(#methods)*)
      (max_cost_term, cost_record)
    else
      let cost_term = Costterms.create_cost_term (List.nth mc_row_j k) (List.nth mf_row_i k) in (*WC: O(1 + #variables + #variables)*)
      let new_max_cost_term = get_max_cost_term max_cost_term cost_term in (*WC: O(#complexities + #frequencies)*)
      let updated_cost_record = increment_cost_term_count cost_record cost_term in (*WC: O(#cost terms)*)
      go_through_methods (k+1) mf_row_i mc_row_j new_max_cost_term updated_cost_record

  (*WC: O(#data structures * (#data structures + (#methods * (#variables + complexities + frequencies + cost terms)) + (#complexities + #frequencies + #data structures)))*)
  let rec go_through_data_structures j mf_row_i mc best_max_cost_term best_data_structures costs =
    if j == (List.length mc) then (*WC: O(#data structures)*)
      (best_max_cost_term, best_data_structures, costs)
    else
      let (max_cost_term_j, cost_record_j) = go_through_methods 0 mf_row_i (List.nth mc j) (init_cost_term) (init_cost_record) in (*WC: O(#methods * (#variables + complexities + frequencies + cost terms))*)
      let updated_costs = add_to_end_of_list costs cost_record_j in (*WC: O(#data structures)*)
      let (new_best_max_cost_term, new_best_data_structures) = get_new_best_max_cost_term_and_best_data_structures best_max_cost_term best_data_structures max_cost_term_j j in (*WC: O(#complexities + #frequencies + #data structures)*)
      go_through_data_structures (j+1) mf_row_i mc new_best_max_cost_term new_best_data_structures updated_costs

  (*WC: O(#variables * (#variables (#data structures * (#data structures + (#methods * (#variables + complexities + frequencies + cost terms)) + (#complexities + #frequencies + #data structures))) + (#data structures^3)))*)
  let rec go_through_variables i mf mc selected_data_structures =
    if i == List.length mf then (*WC: O(#variables)*)
      selected_data_structures
    else
      let (best_max_cost_term, best_data_structures, costs) = go_through_data_structures 0 (List.nth mf i) mc (init_cost_term) [] [] in (*WC: O(#data structures * (#data structures + (#methods * (#variables + complexities + frequencies + cost terms)) + (#complexities + #frequencies + #data structures)))*)
      let best_data_structure_choice = get_top_data_structures best_max_cost_term best_data_structures costs in (*WC: O(#data structures^3)*)
      let updated_selected_data_structures = add_to_end_of_list selected_data_structures best_data_structure_choice in (*WC: O(#data structures)*)
      go_through_variables (i+1) mf mc updated_selected_data_structures

  let main mf =
    let mc = Sequenceinfo.get_mc in (*WC: O(1)*)
    let selected_data_structures = go_through_variables 0 mf mc [] in
    selected_data_structures (*WC: O(#variables * (#variables (#data structures * (#data structures + (#methods * (#variables + complexities + frequencies + cost terms)) + (#complexities + #frequencies + #data structures))) + (#data structures^3)))*)
end

open Dssa
