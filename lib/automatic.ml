open Util
open Tactic
open Expr

let automatic (lines:string list) : unit = 
  (*Le premier element de lines est le goal*)
  let goal = (match parse_type (List.hd lines) with
    | Goal(_, a) -> a
    | _ -> failwith "No goal supplied."
  ) in
  let term = ref (parse_type (List.hd lines)) in
  let tactics = ref (List.tl lines) in
  let finished = ref false in

  while !tactics <> [] && not !finished do
    let myterm = numerote !term in
    let mygoals = get_goals myterm in
    let mygoal = match mygoals with
      | [] -> None
      | goal :: _ -> Some goal
    in
    let tactic = List.hd !tactics in
    tactics := List.tl !tactics;
    try
      let (newterm, is_finished) = handle_tactic mygoal myterm (parse_tactic tactic) in
      term := newterm;
      finished := is_finished;
    with
    | GoalRemaining ->
        print_endline "Qed impossible: there are remaining goals."
    | NoFocusedGoal ->
        print_endline "No focused goal: only Qed. can be used now."
  done;

  (*We finished*)
  (*We reduce the witness*)
  term := reduce !term;
  (*We show a cool message*)
  print_endline "Witness of the proof :";
  affiche_lam !term; print_newline ();
  if not !finished then
    failwith "Proof ended before Qed."
  else (
    print_endline "Typechecking...";
    try 
      typecheck empty_env (!term) goal;
      print_endline "Typechecking was a success !!";
    with Type_error -> failwith "Typechecking failed...";
  )
;;
