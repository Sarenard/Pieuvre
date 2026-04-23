open Expr
open Util
open Tactic

let affiche_context (gamma:context) : unit =
  List.iter
    (fun (x, ty) ->
      print_string x;
      print_string " : ";
      affiche_lam ty;
      print_newline ())
    (List.rev gamma)
;;

let affiche_goal (_i, gamma, ty) : unit =
  print_newline ();
  print_string "Goal :";
  print_newline ();
  affiche_context gamma;
  print_string "----------------";
  print_newline ();
  affiche_lam ty;
  print_newline ()
;;

let interactive_step (term:lambdaterm) : lambdaterm option = 
  let term = numerote term in
  let mygoals = get_goals term in

  let mygoal = match mygoals with
  | [] ->
      print_newline ();
      print_endline "No goals remaining !. Type Qed. to finish.";
      None
  | mygoal :: _ ->
      affiche_goal mygoal;
      Some mygoal
  in

  print_string "> ";
  let input = read_line () in
  match mygoal with
  | Some(goal) -> (
    let lexbuf = Lexing.from_string input in
    let tactic = Parser.tactic_dot Lexer.token lexbuf in
    print_string "Tactique : ";
    print_string (show_tactic tactic);
    print_newline ();
    let return_term = handle_tactic goal empty_env term tactic in
    if get_goals return_term = [] then None else Some(return_term)
  )
  | None -> (
      if input = "Qed." then None else Some(term)
  )
;;

let interactive (term:lambdaterm) : unit = 
  let goal = (match term with
    | Goal(_, a) -> a
    | _ -> failwith "No goal supplied."
  ) in
  let current = ref term in
  let continue = ref true in

  while !continue do
    match interactive_step !current with
    | Some new_term ->
        current := new_term
    | None ->
        continue := false
  done;

  (*We finished*)
  (*We reduce the witness*)
  current := reduce !current;
  (*We show a cool message*)
  print_newline ();
  print_endline "No goals remaining.";
  print_endline "Witness of the proof :";
  affiche_lam !current; print_newline ();
  print_endline "Typechecking...";
  try 
    typecheck empty_env (!current) goal;
    print_endline "Typechecking was a success !!";
  with Type_error -> print_endline "There is an error somewhere...";
;;
