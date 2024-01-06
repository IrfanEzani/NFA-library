(* NFA (Non-deterministic Finite Automaton) Operations *)

type ('state, 'symbol) transition = 'state * 'symbol option * 'state

type ('state, 'symbol) nfa = {
  alphabet: 'symbol list;
  states: 'state list;
  initial_state: 'state;
  final_states: 'state list;
  transitions: ('state, 'symbol) transition list;
}

(* Utility Functions *)

(* Converts a string to a list of characters *)
let string_to_char_list (str: string) : char list =
  let rec explode index result =
    if index < 0 then result else explode (index - 1) (str.[index] :: result)
  in
  explode (String.length str - 1) []

(* NFA Operations *)

(* Retrieves a list of next states reachable from a given state with a specific symbol *)
let rec find_next_states transitions current_state symbol =
  match transitions with
  | [] -> []
  | (state, transition_symbol, next_state) :: remaining_transitions ->
      if state = current_state && transition_symbol = symbol 
        then next_state :: find_next_states remaining_transitions current_state symbol
      else find_next_states remaining_transitions current_state symbol

(* Moves the NFA to the next states based on the current states and a given symbol *)
let transition_states (nfa: ('state, 'symbol) nfa) (current_states: 'state list) (symbol: 'symbol option) : 'state list =
  let rec aux states accumulator =
    match states with
    | [] -> accumulator
    | state::remaining_states ->
        let next_states = find_next_states nfa.transitions state symbol in
        aux remaining_states (union next_states accumulator)
  in
  aux current_states []

(* Computes the epsilon closure of the given states *)
let epsilon_closure (nfa: ('state, 'symbol) nfa) (states: 'state list) : 'state list =
  let rec aux current_states new_states accumulator =
    match current_states with
    | [] -> union accumulator new_states
    | state::remaining_states ->
        let epsilon_reachable_states = transition_states nfa [state] None in
        let newly_added_states = diff epsilon_reachable_states accumulator in
        let updated_accumulator = insert_all epsilon_reachable_states accumulator in
        aux (union remaining_states newly_added_states) (union new_states newly_added_states) updated_accumulator
  in
  aux states states []

(* Checks if any of the current states is a final state *)
let is_accepting_state (nfa: ('state, 'symbol) nfa) (states: 'state list) : bool =
  let rec check states =
    match states with
    | [] -> false
    | state::remaining_states -> 
      if elem state nfa.final_states then true else check remaining_states
  in
  check states

(* Determines if the NFA accepts a given string *)
let nfa_accepts_string (nfa: ('state, char) nfa) (input_string: string) : bool =
  let rec aux characters current_states =
    match characters with
    | [] -> is_accepting_state nfa current_states
    | character :: remaining_characters ->
        let next_states = transition_states nfa current_states (Some character) in
        let epsilon_reachable_states = epsilon_closure nfa next_states in
        aux remaining_characters epsilon_reachable_states
  in
  aux (string_to_char_list input_string) (epsilon_closure nfa [nfa.initial_state])


(* Conversion from NFA to DFA using Subset Construction *)

(* Generates new states for the DFA based on the NFA's transitions *)
let generate_dfa_states (nfa: ('state, 'symbol) nfa) (current_states: 'state list) : 'state list list = 
  map (fun symbol -> epsilon_closure nfa (transition_states nfa current_states (Some symbol))) nfa.alphabet

(* Generates new transitions for the DFA based on the NFA's transitions *)
let generate_dfa_transitions (nfa: ('state, 'symbol) nfa) (current_states: 'state list) : (('state list, 'symbol) transition) list =
  fold_left (fun accumulator symbol -> 
    (current_states, symbol, 
      (epsilon_closure nfa (transition_states nfa current_states (Some symbol)))
    )::accumulator
  ) [] (map (fun symbol -> Some symbol) nfa.alphabet)

(* Determines the final states for the DFA *)
let determine_dfa_final_states (nfa: ('state, 'symbol) nfa) (current_states: 'state list) : 'state list list =
  if is_accepting_state nfa current_states then [current_states] else []

(* One step of NFA to DFA conversion *)
let convert_nfa_to_dfa_step (nfa: ('state, 'symbol) nfa) (dfa: ('state list, 'symbol) nfa) (marked_states: 'state list list) =
  let rec loop dfa marked_states accumulated_finals =
    match marked_states with
    | [] -> { alphabet = dfa.alphabet;
              states = dfa.states @ accumulated_finals;
              initial_state = dfa.initial_state;
              final_states = accumulated_finals;
              transitions = dfa.transitions }

    | state::remaining_states ->
      let new_states = generate_dfa_states nfa state in
      let new_marked_states = 
        if subset new_states dfa.states 
          then remaining_states else union new_states remaining_states in
      let new_finals = determine_dfa_final_states nfa state in
      loop { alphabet = dfa.alphabet;
             initial_state = dfa.initial_state;
             states = union dfa.states new_states;
             final_states = dfa.final_states;
             transitions = union dfa.transitions (generate_dfa_transitions nfa state) }
           new_marked_states (accumulated_finals @ new_finals)

  in
  let initial_dfa_state = epsilon_closure nfa [nfa.initial_state] in
  loop { alphabet = nfa.alphabet;
         initial_state = initial_dfa_state;
         states = [initial_dfa_state];
         final_states = [];
         transitions = [] } [initial_dfa_state] (determine_dfa_final_states nfa initial_dfa_state)

(* Converts an NFA to a DFA *)
let convert_nfa_to_dfa (nfa: ('state, 'symbol) nfa) =
  convert_nfa_to_dfa_step nfa { alphabet = nfa.alphabet;
                                states = [];
                                initial_state = [];
                                final_states = [];
                                transitions = [] } []
