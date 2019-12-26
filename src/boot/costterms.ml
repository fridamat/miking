open Complexities
open Frequencies

type cost_terms = Complexities.complexity * Frequencies.frequency

let get_complexity (complexity, frequency) = complexity (*WC: O(1)*)
let get_frequency (complexity, frequency) = frequency (*WC: O(1)*)

let create_cost_term complexity frequency = (complexity, frequency)

let to_string (complexity, frequency) =
  "(" ^ (Frequencies.to_string frequency) ^ ", " ^ (Complexities.to_string complexity) ^ ")"
