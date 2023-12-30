open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)

(* return  list next states that we can reach from q using s. *)
let rec get_next_states delta q s =
  match delta with
  | [] -> []
  | (state, input, next) :: rest ->
      if state = q && input = s 
        then next :: get_next_states rest q s
      else get_next_states rest q s



let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
  let rec move_aux qs acc =
    match qs with
    | [] -> acc
    | q::rest ->
        let next_states = get_next_states nfa.delta q s in
        move_aux rest (union next_states acc)
  in
  move_aux qs []

  
  let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
    let rec e_closure_aux qs a acc =
    match qs with
    | [] -> union acc a
    | q::rest ->
        let qs' = move nfa [q] None in
        let new_states = diff qs' acc in
        let acc' = insert_all qs' acc in
        e_closure_aux (union rest new_states) (union a new_states) acc'
  in
  e_closure_aux qs qs []

  
let rec end_state nfa qs =
  let rec end_state_aux qs =
    match qs with
    | [] -> false
    | q::rest -> if (elem q nfa.fs) then true else (end_state_aux rest)
  in
  end_state_aux qs

let accept (nfa: ('q, char) nfa_t) (s: string) : bool =
  let rec accept_aux cs qs =
    match cs with
    | [] -> end_state nfa qs
    | c :: rest ->
        let next_states = move nfa qs (Some c) in
        let next_qs = e_closure nfa next_states in
        accept_aux rest next_qs
  in
  accept_aux (explode s) (e_closure nfa [nfa.q0])


(*******************************)
(* Part 2: Subset Construction *)
(*******************************)
let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list = 
  map (fun x -> e_closure nfa (move nfa qs (Some x))) nfa.sigma

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  fold_left (fun acc x -> (qs, x, (e_closure nfa (move nfa qs x)))::acc) [] (map (fun x -> Some x) nfa.sigma)

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  if (end_state nfa qs) then [qs] else []


let nfa_to_dfa_step nfa dfa marked_qs =
  let rec loop dfa marked_qs acc_final =
    match marked_qs with
    | [] -> { sigma = dfa.sigma;
              q0 = dfa.q0;
              qs = dfa.qs @ acc_final;
              fs = acc_final;
              delta = dfa.delta }

    | state::rest ->
      let new_states = new_states nfa state in
      let new_marked_qs = 
        if subset new_states dfa.qs 
          then rest else union new_states rest in
      let new_finals = new_finals nfa state in
      loop { sigma = dfa.sigma;
             q0 = dfa.q0;
             qs = union dfa.qs new_states;
             fs = dfa.fs;
             delta = union dfa.delta (new_trans nfa state) }
           new_marked_qs (acc_final @ new_finals)

  in
  let r0 = e_closure nfa [nfa.q0] in
  loop { sigma = nfa.sigma;
         q0 = r0;
         qs = [r0];
         fs = [];
         delta = [] } [r0] (new_finals nfa r0)

let nfa_to_dfa nfa =
  nfa_to_dfa_step nfa { sigma = nfa.sigma;
                        qs = [];
                        q0 = [];
                        fs = [];
                        delta = [] } []
