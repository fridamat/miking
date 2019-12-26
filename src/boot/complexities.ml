exception UnknownComplexity

type complexity = None | Const | Logn | X1 | X2

(*Each complexity is identified by a name and its position in the list decides its rank. If we have the list ["f1","f2","f3","f4"...] then the rank of f1 < the rank of f2, the rank of f2 < the rank of f3, the rank of f3 < the rank of f4, and so forth.*)
let get_complexities =
  [Const; Logn; X1; X2;]

(*Takes in a list of complexities, a complexity and an index, and checks if the element at position index in the list is equal to the complexity we are looking for. If there is a match, then we return the index, which corresponds to the rank of the complexity. Otherwise, we recursively call the method with an incremented index until we've reached the end of the list or find a match.*)
let rec get_complexity_rank_helper complexities complexity index =
  if complexity == None then
    0
  else if (List.length complexities) == index then
    raise UnknownComplexity
  else if (List.nth complexities index) = complexity then
    index (*The index corresponds to the rank*)
  else
    get_complexity_rank_helper complexities complexity (index+1)

(*Takes in a complexity, and calls a helper method that finds the index/rank of that complexity.*)
let get_complexity_rank complexity =
  get_complexity_rank_helper get_complexities complexity 0 (*0 is the start index*)

(*Takes in a complexity of rank r, and if there is a complexity with rank r-1, then this complexity is returned. Otherwise, "None" is returned which signals that there is no such complexity.*)
let get_next_lower_complexity complexity =
  let complexity_rank = get_complexity_rank complexity in
  match complexity_rank with
  | 0 -> None
  | _ -> List.nth get_complexities (complexity_rank-1)

(*WC: O(#complexities)*)
(*Takes in two complexities (complexity_1 and complexity_2) and compares their ranks (complexity_rank_1 and complexity_rank_2). Returns 1 if complexity_rank_1 > complexity_rank_2, returns -1 if complexity_rank_1 < complexity_rank_2 and 0 if complexity_rank_1 = complexity_rank_2.*)
let compare_complexities complexity_1 complexity_2 =
  if complexity_1 == None then
    -2
  else if complexity_2 == None then
    2
  else
    let complexity_rank_1 = get_complexity_rank complexity_1 in (*WC: O(#complexities)*)
    let complexity_rank_2 = get_complexity_rank complexity_2 in (*WC: O(#complexities)*)
    if complexity_rank_1 > complexity_rank_2 then
      1
    else if complexity_rank_1 < complexity_rank_2 then
      -1
    else 0

let to_string complexity =
  match complexity with
  | None -> "complexity not set"
  | Const -> "constant"
  | Logn -> "logn"
  | X1 -> "x^1"
  | X2 -> "x^2"
