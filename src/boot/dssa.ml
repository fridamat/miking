(*TODO: Should get_top_data_structures return a list of top elements or just the one?*)

open Complexities
open Costterms
open Frequencies
open Pervasives

exception UnknownComparisonResult
exception UnknownCostTerm
exception NoDataStructureOptions

module Dssa = struct
  (*--- Print methods ---*)

  (*TODO: Write comment*)
  let pair_to_string (a,b) =
    (Costterms.to_string a) ^ " with count " ^ (Pervasives.string_of_int b) ^ ", "

  (*TODO: Write comment*)
  let rec get_cost_record_string cost_record =
    match cost_record with
    | [] -> "\n"
    | hd::tl ->
      (pair_to_string hd) ^ (get_cost_record_string tl)

  (*TODO: Write comment*)
  let print_cost_record cost_record =
    Printf.printf "The cost record:\n%s" (get_cost_record_string cost_record)

  (*--- Helper methods ---*)

  (*Takes in a list (l) and an element (e) and adds the element to the end of the list.*)
  let rec add_to_end_of_list l e =
    match l with
    | [] -> e::[]
    | hd::tl -> hd::(add_to_end_of_list tl e)

  (*Takes in two complexities (complexity_1 and complexity_2) and compares them with the comparer function from the Complexities file. Returns 2 if complexity_2 = None, 1 if complexity_1 > complexity_2, 0 if complexity_1 = complexity_2, -1 if complexity_1 < complexity_2 and -2 if complexity_1 = None.*)
  let compare_complexities complexity_1 complexity_2 =
    match Complexities.compare_complexities complexity_1 complexity_2 with
    | 2 -> 2 (*complexity_2 = None*)
    | 1 -> 1 (*complexity_1 > complexity_2*)
    | 0 -> 0 (*complexity_1 = complexity_2*)
    | -1 -> -1 (*complexity_1 < complexity_2*)
    | -2 -> -2 (*complexity_1 = None*)
    | _ -> raise UnknownComparisonResult

  (*Takes in two frequencies (frequency_1 and frequency_2) and compares them with the comparer function from the Frequencies file. Returns 2 if frequency_2 = None, 1 if frequency_1 > frequency_2, 0 if frequency_1 = frequency_2, -1 if frequency_1 < frequency_2 and -2 if frequency_1 = None.*)
  let compare_frequencies frequency_1 frequency_2 =
    match Frequencies.compare_frequencies frequency_1 frequency_2 with
    | 2 -> 2 (*frequency_2 = None*)
    | 1 -> 1 (*frequency_1 > frequency_2*)
    | 0 -> 0 (*frequency_1 = frequency_2*)
    | -1 -> -1 (*frequency_1 < frequency_2*)
    | -2 -> -2 (*frequency_1 = None*)
    | _ -> raise UnknownComparisonResult

  (*Takes in two cost terms (cost_term_1 and cost_term_2) and collects the complexities (complexity_1 and complexity_2) and frequencies (frequency_1 and frequency_2) contained in respective cost term. Starts by comparing the complexities. Returns 2 if complexity_2 = None, 1 if complexity_1 > complexity_2, -1 if complexity_1 < complexity_2 and -2 if complexity_1 = None. If complexity_1 = complexity_2, we want to compare the frequencies as well. Returns 2 if frequency_2 = None, 1 if frequency_1 > frequency_2, 0 if frequency_1 = frequency_2, -1 if frequency_1 < frequency_2 and -2 if frequency_1 = None. This means that if a -2 or 2 is returned this signals that the first or the second cost term have no value.*)
  let compare_cost_terms cost_term_1 cost_term_2 =
    let complexity_1 = Costterms.get_complexity cost_term_1 in
    let complexity_2 = Costterms.get_complexity cost_term_2 in
    let frequency_1 = Costterms.get_frequency cost_term_1 in
    let frequency_2 = Costterms.get_frequency cost_term_2 in
    match compare_complexities complexity_1 complexity_2 with
    | 2 -> 2 (*complexity_2 = None*)
    | 1 -> 1 (*complexity_1 > complexity_2*)
    | 0 -> (
        (*complexity_1 = complexity_2, so we want to compare the frequencies*)
        match compare_frequencies frequency_1 frequency_2 with
        | 2 -> 2 (*frequency_2 = None*)
        | 1 -> 1 (*frequency_1 > frequency_2*)
        | 0 -> 0 (*frequency_1 = frequency_2*)
        | -1 -> -1 (*frequency_1 < frequency_2*)
        | -2 -> -2 (*frequency_1 = None*)
        | _ -> raise UnknownComparisonResult)
    | -1 -> -1 (*complexity_1 < complexity_2*)
    | -2 -> -2 (*complexity_1 = None*)
    | _ -> raise UnknownComparisonResult

             (*Takes in the best max cost term so far (best_max_cost_term), the corresponding list of best data structures so far (best_data_structures), a contender cost term (contender_cost_term) and the corresponding contender data structure (contender_data_structure). We want to get the best cost term (the smallest one) of best_max_cost_term and contender_cost_term and the corresponding data structures. Returns the contender cost term and a list containing only the contender data structure if best_max_cost_term = None or if best_max_cost_term > contender_cost_term. Returns the best_max_cost_term and a list containing both best_data_structures and contender_data_structure if best_max_cost_term = contender_cost_term. Returns best_max_cost_term and best_data_structures if contender_cost_term = None or best_max_cost_term < contender_cost_term.*)
  let get_new_best_max_cost_term_and_best_data_structures best_max_cost_term best_data_structures contender_cost_term contender_data_structure =
    match compare_cost_terms best_max_cost_term contender_cost_term with
    | 2 -> (best_max_cost_term, best_data_structures) (*contender_cost_term = None*)
    | 1 -> (contender_cost_term, [contender_data_structure]) (*best_max_cost_term > contender_cost_term*)
    | 0 -> (best_max_cost_term, (add_to_end_of_list best_data_structures contender_data_structure)) (*best_max_cost_term = contender_cost_term*)
    | -1 -> (best_max_cost_term, best_data_structures) (*best_max_cost_term < contender_cost_term*)
    | -2 -> (contender_cost_term, [contender_data_structure]) (*best_max_cost_term = None*)
    | _ -> raise UnknownComparisonResult

  (*Takes in two cost terms. Returns cost_term_1 if cost_term_2 = None, cost_term_1 > cost_term_2 or cost_term_1 = cost_term_2. Returns cost_term_2 if cost_term_1 = None or cost_term_1 < cost_term_2.*)
  let get_max_cost_term cost_term_1 cost_term_2 =
    match compare_cost_terms cost_term_1 cost_term_2 with
    | 2 -> cost_term_1 (*cost_term_2 = None*)
    | 1 -> cost_term_1 (*cost_term_1 > cost_term_2*)
    | 0 -> cost_term_1 (*cost_term_1 = cost_term_2*)
    | -1 -> cost_term_2 (*cost_term_1 < cost_term_2*)
    | -2 -> cost_term_2 (*cost_term_1 = None*)
    | _ -> raise UnknownComparisonResult

  (*Takes in a cost term (cost_term), a list of data structures (data_structures) and a list of cost records (costs). Returns the list of data structures if the frequency of the cost term is zero, which means it does not affect the code. Otherwise, for each data structure this method checks if the cost term count is 0 and in that case appends that data structure to a list. This list is returned once we've gone through all data structures.*)
  let rec get_data_structures_with_zero_count_for_cost_term cost_term data_structures costs =
    let frequency = Costterms.get_frequency cost_term in
    match frequency with
    | Frequencies.Zero -> data_structures (*We do not care about cost terms with zero frequency*)
    | _ ->
      (match data_structures with
       | [] -> [] (*We've reached the end of the list of data structures*)
       | ds_hd::ds_tl ->
         let curr_cost_record = List.nth costs ds_hd in
         let cost_term_count = List.assoc cost_term curr_cost_record in
         if cost_term_count == 0 then
           ds_hd::(get_data_structures_with_zero_count_for_cost_term cost_term ds_tl costs)
         else
           get_data_structures_with_zero_count_for_cost_term cost_term ds_tl costs
      )

  (*Takes in a cost term (cost_term), a list of data structures (data_structures), a list of cost records (costs), the min count so far (min_count) and the list of data structures that have the min_count for the cost_term. Returns the list of data structures if the frequency of the cost term is zero, which means it does not affect the code. Otherwise, for each data structure this method checks if the cost term count is a new minimum count and sets contenders to be the current data structure. If the cost term count is equal to the min_count, the method appends the current data structure to the list of contenders. Otherwise, the min_count and contenders list remains the same. This list and the min_count are returned once we've gone through all data structures.*)
  let rec get_data_structures_with_min_count_for_cost_term_helper cost_term data_structures costs min_count contenders =
    let frequency = Costterms.get_frequency cost_term in
    match frequency with
    | Frequencies.Zero -> data_structures (*We do not care about cost terms with zero frequency*)
    | _ ->
      (match data_structures with
       | [] -> contenders (*We've reached the end of the list of data structures*)
       | ds_hd::ds_tl ->
         let curr_cost_record = List.nth costs ds_hd in
         let cost_term_count = List.assoc cost_term curr_cost_record in
         if cost_term_count < min_count then
           let new_min_count = cost_term_count in
           let new_contenders = [ds_hd] in
           get_data_structures_with_min_count_for_cost_term_helper cost_term ds_tl costs new_min_count new_contenders
         else if cost_term_count == min_count then
           let updated_contenders = add_to_end_of_list contenders ds_hd in (*We add the current data structure to the list of contenders*)
           get_data_structures_with_min_count_for_cost_term_helper cost_term ds_tl costs min_count updated_contenders
         else
           (*The minimum count is still minimum and the list of contenders remains the same*)
           get_data_structures_with_min_count_for_cost_term_helper cost_term ds_tl costs min_count contenders
      )

  (*Takes in a cost term (cost_term), a list of data structures and a list of cost records, and calls a helper method that finds and returns the data structures that share the minimum count for this cost term.*)
  let get_data_structures_with_min_count_for_cost_term cost_term data_structures costs =
    (*Calls method with min_count as the maximal int and contenders as an empty list*)
    get_data_structures_with_min_count_for_cost_term_helper cost_term data_structures costs max_int []

  (*Takes in a cost term and uses its frequency and complexity to find the next lower cost term. If both the next lower frequency and the next lower complexity are None, then there is no lower cost term. If the next lower frequency is None, but the next lower complexity has another value, then the next lower cost term is the maximum frequency together with the next lower complexity. Otherwise, the next lower cost term is the current complexity together with the next lower frequency.*)
  let get_next_lower_cost_term cost_term =
    let frequency = Costterms.get_frequency cost_term in
    let complexity = Costterms.get_complexity cost_term in
    let next_lower_frequency = Frequencies.get_next_lower_frequency frequency in
    let next_lower_complexity = Complexities.get_next_lower_complexity complexity in
    match (next_lower_frequency, next_lower_complexity) with
    | (Frequencies.None, Complexities.None) -> Costterms.create_cost_term next_lower_complexity next_lower_frequency (*Returns the empty cost term - that is, (None, None)*)
    | (Frequencies.None, _) -> Costterms.create_cost_term next_lower_complexity Frequencies.Many
    | _ -> Costterms.create_cost_term complexity next_lower_frequency

  (*Takes in a cost term (curr_cost_term), a list containing the best data structures found so far (best_data_structures) and a list containing cost records for all data structures. If the cost term has no value - that is, (None, None) - then no more comparisons can be done and we simply return the list with the best data structures. If the list of data structures is empty, then something is wrong. Otherwise, we get the data structures with a 0 count for the cost term and if there are some call the method recursively for the next lower cost term with these. If there were no data structures with 0 count, we get the ones with the minimum count for the cost term, and call the method recursively for the next lower cost term with these.*)
  let rec get_top_data_structures curr_cost_term best_data_structures costs =
    match (curr_cost_term, best_data_structures) with
    | ((Complexities.None, Frequencies.None), _) -> best_data_structures (*There are no more cost terms to compare*)
    | (_, []) -> raise NoDataStructureOptions (*There are no data structures for us to choose from*)
    | _ ->
      let contenders = get_data_structures_with_zero_count_for_cost_term curr_cost_term best_data_structures costs in
      let next_cost_term = get_next_lower_cost_term curr_cost_term in
      (match contenders with
       | [] ->
         (*We found no contenders with 0 count, so we want to find the ones with minimum count instead*)
         let new_contenders = get_data_structures_with_min_count_for_cost_term curr_cost_term best_data_structures costs in
         (*We have our contenders with minimum count for the current cost term, and want to compare the next lower cost term*)
         get_top_data_structures next_cost_term new_contenders costs
       | _ ->
         (*We have our contenders with 0 count for the current cost term, and want to compare the next lower cost term*)
         get_top_data_structures next_cost_term contenders costs
      )

  (*Takes in a cost record (cost_record) and a cost term (cost_term). Raises an exception if the cost record doesn't contain the cost term. Otherwise, we incremenet the count for the cost term by one and updates and returns the cost record.*)
  let increment_cost_term_count cost_record cost_term =
    (*Check if cost record contains cost term*)
    if List.mem_assoc cost_term cost_record then
      (*Get current count for cost term*)
      let curr_count = List.assoc cost_term cost_record in
      (*Remove old entry*)
      let updated_record = List.remove_assoc cost_term cost_record in
      (*Add incremented entry to cost record*)
      add_to_end_of_list updated_record (cost_term, (curr_count+1))
    else
      raise UnknownCostTerm

  (*Takes in a frequency and a list of complexity and creates a cost term for each frequency-complexity combination and adds these to a list of cost terms. *)
  let rec combine_complexities_with_frequency frequency complexities =
    match complexities with
    | [] -> []
    | comp_hd::comp_tl -> (Costterms.create_cost_term comp_hd frequency)::(combine_complexities_with_frequency frequency comp_tl)

  (*Takes in a list of frequencies and complexities, and returns a list containing all possible cost terms - that is, frequency-complexity combinations.*)
  let rec build_cost_terms frequencies complexities =
    match frequencies with
    | [] -> [] (*We've reached the end of the list of frequencies*)
    | freq_hd::freq_tl ->
      List.append (combine_complexities_with_frequency freq_hd complexities) (build_cost_terms freq_tl complexities)

  (*Takes in a list of cost terms and creates an associatio list that connects each cost term to the initial count value, which is 0.*)
  let rec init_cost_record_helper cost_terms =
    match cost_terms with
    | [] -> [] (*We've reached the end of the list of cost terms*)
    | ct_hd::ct_tl ->
      (*Add pair cost term head and start count - that is, (ct_hd, 0) - to cost record*)
      (ct_hd,0)::(init_cost_record_helper ct_tl)

  (*Initiates a cost record where each cost term is linked to the initial count value, which is 0. This is returned in the shape of an association list.*)
  let init_cost_record =
    let cost_terms = build_cost_terms Frequencies.get_frequencies Complexities.get_complexities in init_cost_record_helper cost_terms

  (*Initiates a cost term.*)
  let init_cost_term = (Complexities.None, Frequencies.None) (*TODO: Make into its own method in Costterms?*)

  (*--- Main methods ---*)

  (*Takes in a method index (k), row i from the method frequency matrix (mf_row_i), row j from the method complexity matrix (mc_row_j), the maximum cost term so far for j and a cost record for keeping track of the cost for data structure j. Creates the cost term for each method k on data structure j, checks if this is a new maximum cost term (and keeps track of the maximum so far) and increments the count for the number of occurrences of this cost term in the cost record. Does this for all methods, and then returns the maximum cost term and cost record.*)
  let rec go_through_methods k mf_row_i mc_row_j max_cost_term cost_record =
    (*Check if we've gone through all methods*)
    if k == (List.length mf_row_i) then
      (*We return the max cost term and cost record over all methods for data structure j*)
      (max_cost_term, cost_record)
    else
      let cost_term = Costterms.create_cost_term (List.nth mc_row_j k) (List.nth mf_row_i k) in
      let new_max_cost_term = get_max_cost_term max_cost_term cost_term in
      let updated_cost_record = increment_cost_term_count cost_record cost_term in
      go_through_methods (k+1) mf_row_i mc_row_j new_max_cost_term updated_cost_record

  (*Takes in a data structure index (j), row i from the method frequency matrix (mf_row_i),  the method complexity matrix (mc), the maximum cost term so far for variable i and a list of cost records for keeping track of the costs for data structure for variable i. Goes through all methods for each data structure j to get its cost record and to keep track of the best maximum cost term over all data structures for variable i. Returns the best max cost term over all data structures for i, the corresponding data structures and the cost records when it has gone through all the data structures.*)
  let rec go_through_data_structures j mf_row_i mc best_max_cost_term best_data_structures costs =
    (*Check if we've gone through all data structures*)
    if j == (List.length mc) then
      (*We return the best max cost term and best data structures for variable i*)
      (best_max_cost_term, best_data_structures, costs)
    else
      (*Get the max cost term and cost record for data structure j*)
      let (max_cost_term_j, cost_record_j) = go_through_methods 0 mf_row_i (List.nth mc j) (init_cost_term) (init_cost_record) (*TODO: Create an init_count method?*) in
      let updated_costs = add_to_end_of_list costs cost_record_j in (*TODO: Make costs into an assoc list?*)
      (*Check if data structure j is the best option for variable i so far given its cost term*)
      let (new_best_max_cost_term, new_best_data_structures) = get_new_best_max_cost_term_and_best_data_structures best_max_cost_term best_data_structures max_cost_term_j j in
      go_through_data_structures (j+1) mf_row_i mc new_best_max_cost_term new_best_data_structures updated_costs

  (*Takes in a variable index (i), the method frequency matrix (mf), the method complexity matrix (mc) and a list of the selected data structures for variables so far. Goes through all data structures for variable i to get the best max cost term, the corresponding list of best data structures and a list of the cost records for all data structures. Then calls a comparer function to get the top data structures from the list of data structures found in the previous step. Then, adds this top data structures as the selected ones for variable i by adding it to the list of selected data structures. This list is then returned when we've gone through all variables.*)(*TODO:Test*)
  let rec go_through_variables i mf mc selected_data_structures =
    (*Check if we've gone through all variables*)
    if i == List.length mf then
      selected_data_structures (*Return the selected data structures for all variables*)
    else
      (*Get the best max cost term, best data structures and costs for all data structures and variable i*)
      let (best_max_cost_term, best_data_structures, costs) = go_through_data_structures 0 (List.nth mf i) mc (init_cost_term) [] [] in
      (*Get the best of the best*)
      let best_data_structure_choice = get_top_data_structures best_max_cost_term best_data_structures costs in
      (*SO FAR SO GOOD*)
      let updated_selected_data_structures = add_to_end_of_list selected_data_structures best_data_structure_choice in
      go_through_variables (i+1) mf mc updated_selected_data_structures

  let main mf =
    let mc =
      [[Complexities.Logn;Complexities.Logn;Complexities.Logn; Complexities.Logn;Complexities.Logn;Complexities.Logn;Complexities.Logn;Complexities.Logn;Complexities.Logn;Complexities.Logn;Complexities.Logn;Complexities.Logn;Complexities.Logn;Complexities.Logn;Complexities.Logn;Complexities.Logn;Complexities.Logn;Complexities.Logn;Complexities.Logn;Complexities.Logn;];] in (*TODO: Collect from file*)
    let selected_data_structures = go_through_variables 0 mf mc [] in
    selected_data_structures
end

open Dssa
