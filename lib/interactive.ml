open Expr
open Util
open Tactic

(*
Shows the context as a neat list
a : A
...
n : N
*)
let affiche_context (gamma:context) : unit =
  List.iter
    (fun (x, ty) ->
      print_string x;
      print_string " : ";
      print_endline (affiche_lam ty);
    )
    (List.rev gamma.gamma)
;;

(*
The interactive UI
An example :
n : N
N : Type
=================
eq N n n
*)
let affiche_goal (_i, gamma, ty) : unit =
  print_newline ();
  print_string "Goal :";
  print_newline ();
  affiche_context gamma;
  print_string "----------------";
  print_newline ();
  print_endline (affiche_lam ty);
;;

(*
Runs one step of the loop "show the UI" + "asks for a tactic"
*)
let interactive_step (term:lambdaterm) 
: (lambdaterm * bool) (*(term, should we continue)*) = 
  let term = numerote term in
  let mygoals = get_goals empty_env term in

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
    let tactic = Parser.main_tactic Lexer.token lexbuf in
    print_string "Tactic : ";
    print_string (show_tactic tactic);
    print_newline ();
    let return_term = handle_tactic goal empty_env term tactic in
    (return_term, (get_goals empty_env return_term <> []))
  )
  | None -> (
      (term, input <> "Qed.")
  )
;;

(*
The main loop, we continue until we get a Qed.
*)
let interactive () : unit = 
  print_string "Goal : ";
  let input = read_line () in
  let lexbuf = Lexing.from_string input in
  let parse () = Parser.main_term Lexer.token lexbuf in
  let goal = parse () in
  let term = Goal(0, goal) in
  let current = ref term in
  let continue = ref true in

  while !continue do
    let term, cont = interactive_step !current in
    current := term;
    continue := cont;
  done;

  (*We finished*)
  (*We reduce the witness*)
  current := reduce empty_env !current;
  (*We show a cool message because we prooved the goal*)
  print_newline ();
  print_endline "No goals remaining.";
  print_endline "Witness of the proof :";
  print_endline (affiche_lam !current);
  print_endline (affiche_lam goal);
  print_endline "Typechecking...";
  try 
    typecheck empty_env (!current) goal;
    print_endline "Typechecking was a success !!";
  with Type_error -> print_endline "There is an error somewhere...";
;;
