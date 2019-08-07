exception UnknownFrequency

type frequency = None | Zero | One | Many

(*Each frequency is identified by a name and its position in the list decides its rank. If we have the list ["f1","f2","f3","f4"...] then the rank of f1 < the rank of f2, the rank of f2 < the rank of f3, the rank of f3 < the rank of f4, and so forth.*)
let get_frequencies =
  [Zero; One; Many]

(*Takes in a list of frequencies, a frequency and an index, and checks if the element at position index in the list is equal to the frequency we are looking for. If there is a match, then we return the index, which corresponds to the rank of the frequency. Otherwise, we recursively call the method with an incremented index until we've reached the end of the list or find a match.*)
let rec get_frequency_rank_helper frequencies frequency index =
  if frequency == None then
    0
  else if (List.length frequencies) == index then
    raise UnknownFrequency
  else if (List.nth frequencies index) = frequency then
    index (*The index corresponds to the rank*)
  else
    get_frequency_rank_helper frequencies frequency (index+1)

(*Takes in a frequency, and calls a helper method that finds the index/rank of that frequency.*)
let get_frequency_rank frequency =
  get_frequency_rank_helper get_frequencies frequency 0 (*0 is the start index*)

(*Takes in a frequency of rank r, and if there is a frequency with rank r-1, then this frequency is returned. Otherwise, "None" is returned which signals that there is no such frequency.*)
let get_next_lower_frequency frequency =
  let frequency_rank = get_frequency_rank frequency in
  match frequency_rank with
  | 0 -> None (*TODO: Make enum*)
  | _ -> List.nth get_frequencies (frequency_rank-1)

(*Takes in two frequencies (frequency_1 and frequency_2) and compares their ranks (frequency_rank_1 and frequency_rank_2). Returns 1 if frequency_rank_1 > frequency_rank_2, returns -1 if frequency_rank_1 < frequency_rank_2 and 0 if frequency_rank_1 = frequency_rank_2.*)
let compare_frequencies frequency_1 frequency_2 =
  if frequency_1 == None then
    -2
  else if frequency_2 == None then
    2
  else
    let frequency_rank_1 = get_frequency_rank frequency_1 in
    let frequency_rank_2 = get_frequency_rank frequency_2 in
    if frequency_rank_1 > frequency_rank_2 then
      1
    else if frequency_rank_1 < frequency_rank_2 then
      -1
    else 0

let to_string frequency =
  match frequency with
  | None -> "frequency not set"
  | Zero -> "zero"
  | One -> "one"
  | Many -> "many"

let rec translate_mf_assoc_row mf_row fun_names =
  match fun_names with
  | [] -> []
  | hd::tl ->
    let fun_count = List.assoc hd mf_row in
    if fun_count = 0 then
      Zero::(translate_mf_assoc_row mf_row tl)
    else if fun_count = -1 then
      Many::(translate_mf_assoc_row mf_row tl)
    else
      One::(translate_mf_assoc_row mf_row tl)

let rec translate_mf_assoc_list mf_assoc_list fun_names = (*TODO: Test*)
  match mf_assoc_list with
  | [] -> []
  | hd::tl ->
    (translate_mf_assoc_row hd fun_names)::(translate_mf_assoc_list tl fun_names)
