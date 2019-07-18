open Complexities
open Frequencies

type cost_terms = Complexities.complexity * Frequencies.frequency

let get_complexity (complexity, frequency) = complexity
let get_frequency (complexity, frequency) = frequency

let create_cost_term complexity frequency = (complexity, frequency)

let to_string (complexity, frequency) =
  "(" ^ (Frequencies.to_string frequency) ^ ", " ^ (Complexities.to_string complexity) ^ ")"
