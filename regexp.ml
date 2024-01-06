open List
open Nfa
open Sets

(* regex to NFA Converter *)

(* Type definition for regular expressions *)
type regular_expression =
  | EmptyString
  | Character of char
  | Union of regular_expression * regular_expression
  | Concatenation of regular_expression * regular_expression
  | Repetition of regular_expression

(* Generates unique integers for state naming in NFA *)
let generate_unique_state =
  let counter = ref 0 in
  fun () ->
    counter := !counter + 1 ;
    !counter

(* Extracts the first final state from a list of final states *)
let get_first_final_state final_states = 
  match final_states with 
  | [] -> 0
  | state::_ -> state

(* Converts a regular expression to an NFA *)
let rec convert_regexp_to_nfa (regexp: regular_expression) : (int, char) nfa_t = 
  match regexp with
  | EmptyString -> 
    { sigma = []; q0 = 0; qs = [0]; fs = [0]; delta = [] }

  | Character c -> 
    let start_state = generate_unique_state () in 
    let end_state = generate_unique_state () in
    { sigma = [c]; q0 = start_state; qs = [start_state; end_state]; fs = [end_state]; delta = [(start_state, Some c, end_state)] }

  | Union(re1, re2) ->
    let new_start = generate_unique_state () in 
    let new_final = generate_unique_state () in 
    let nfa1 = convert_regexp_to_nfa re1 in 
    let nfa2 = convert_regexp_to_nfa re2 in 
    let combined_states = new_start :: new_final :: nfa1.qs @ nfa2.qs in 
    let combined_transitions = List.map (fun (q, a, q') -> (q, a, q')) (nfa1.delta @ nfa2.delta) in 
    let new_transitions = combined_transitions @
                          [ (new_start, None, nfa1.q0); 
                            (new_start, None, nfa2.q0); 
                            (get_first_final_state nfa1.fs, None, new_final); 
                            (get_first_final_state nfa2.fs, None, new_final); 
                          ] in 
    { sigma = union nfa1.sigma nfa2.sigma; q0 = new_start; qs = combined_states; fs = [new_final]; delta = new_transitions }

  | Concatenation(re1, re2) -> 
    let nfa1 = convert_regexp_to_nfa re1 in 
    let nfa2 = convert_regexp_to_nfa re2 in 
    { sigma = union nfa1.sigma nfa2.sigma;
      q0 = nfa1.q0;
      qs = union nfa1.qs nfa2.qs;
      fs = nfa2.fs;
      delta = union (union nfa1.delta nfa2.delta) [(get_first_final_state nfa1.fs, None, nfa2.q0)]
    }

  | Repetition re -> 
    let start_state = generate_unique_state () in
    let end_state = generate_unique_state () in
    let nfa = convert_regexp_to_nfa re in
    { sigma = nfa.sigma;
      qs = start_state :: end_state :: nfa.qs;
      q0 = start_state;
      fs = [end_state];
      delta = (start_state, None, end_state) ::
              (start_state, None, nfa.q0) ::
              List.map (fun q -> (q, None, end_state)) nfa.fs @
              List.map (fun q -> (q, None, nfa.q0)) nfa.fs @
              nfa.delta
    }

(* Exception for invalid regular expressions *)
exception InvalidRegularExpression of string

(* Token types for regular expression parsing *)
type token =
  | TokenCharacter of char
  | TokenEpsilon
  | TokenUnion
  | TokenRepetition
  | TokenLeftParenthesis
  | TokenRightParenthesis
  | TokenEnd

(* Converts a token to a string representation *)
let string_of_token token =
  match token with
  | TokenCharacter v -> Char.escaped v
  | TokenEpsilon -> "Epsilon"
  | TokenUnion -> "Union"
  | TokenRepetition -> "Repetition"
  | TokenLeftParenthesis -> "LeftParenthesis"
  | TokenRightParenthesis -> "RightParenthesis"
  | TokenEnd -> "End"

(* Tokenizes a string into a list of tokens *)
let tokenize_expression expression =
  let regex_character = Str.regexp "[a-z]" in
  let regex_epsilon = Str.regexp "E" in
  let regex_union = Str.regexp "|" in
  let regex_repetition = Str.regexp "*" in
  let regex_left_parenthesis = Str.regexp "(" in
  let regex_right_parenthesis = Str.regexp ")" in

  let rec tokenize index expr =
    if index >= String.length expr then [TokenEnd]
    else if Str.string_match regex_character expr index then
      TokenCharacter (expr.[index]) :: tokenize (index + 1) expr
    else if Str.string_match regex_epsilon expr index then
      TokenEpsilon :: tokenize (index + 1) expr
    else if Str.string_match regex_union expr index then
      TokenUnion :: tokenize (index + 1) expr
    else if Str.string_match regex_repetition expr index then
      TokenRepetition :: tokenize (index + 1) expr
    else if Str.string_match regex_left_parenthesis expr index then
      TokenLeftParenthesis :: tokenize (index + 1) expr
    else if Str.string_match regex_right_parenthesis expr index then
      TokenRightParenthesis :: tokenize (index + 1) expr
    else raise (InvalidRegularExpression ("Invalid token in expression: " ^ expr))
  in
  tokenize 0 expression

(* Parses a list of tokens into a regular expression *)
let parse_regular_expression token_list =
  let rec parse_union tokens =
    let term, rest = parse_concatenation tokens in
    match lookahead rest with
    | TokenUnion, remainder -> 
        let union_r, final = parse_union remainder in
        (Union (term, union_r), final)
    | _ -> (term, rest)

  and parse_concatenation tokens =
    let factor, rest = parse_repetition tokens in
    match lookahead rest with
    | TokenCharacter _ | TokenEpsilon | TokenLeftParenthesis -> 
        let concatenation_r, final = parse_concatenation rest in
        (Concatenation (factor, concatenation_r), final)
    | _ -> (factor, rest)

  and parse_repetition tokens =
    let base, rest = parse_base tokens in
    match lookahead rest with
    | TokenRepetition, remainder -> (Repetition base, remainder)
    | _ -> (base, rest)

  and parse_base tokens =
    match lookahead tokens with
    | TokenCharacter c, rest -> (Character c, rest)
    | TokenEpsilon, rest -> (EmptyString, rest)
    | TokenLeftParenthesis, rest -> 
        let expr, remainder = parse_union rest in
        (match lookahead remainder with
         | TokenRightParenthesis, final -> (expr, final)
         | _ -> raise (InvalidRegularExpression "Missing right parenthesis"))
    | _ -> raise (InvalidRegularExpression "Invalid base expression")

  and lookahead tokens =
    match tokens with
    | [] -> raise (InvalidRegularExpression "Unexpected end of expression")
    | head :: tail -> (head, tail)

  in
  let parsed_expression, remaining_tokens = parse_union token_list in
  if remaining_tokens = [TokenEnd] then parsed_expression
  else raise (InvalidRegularExpression "Incomplete parsing of expression")

(* Converts a string to a regular expression *)
let string_to_regular_expression str = 
  parse_regular_expression (tokenize_expression str)

(* Converts a string directly to an NFA *)
let string_to_nfa str = 
  convert_regexp_to_nfa (string_to_regular_expression str)
