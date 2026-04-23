open Expr

let get_goals (term:lambdaterm) =
  let rec get_goals_aux (gamma:context) (term:lambdaterm) : (int * context * lambdaterm) list = 
    (
      match term with
      | Var(x) -> []
      | Type -> []
      | Pi(x, a, b) -> [] (*type only*)
      | Func(x, a, b) -> get_goals_aux ((x, a)::gamma) b
      | App(a, b) -> (get_goals_aux gamma a)@(get_goals_aux gamma b)
      | Goal(i, a) -> [(i, gamma, a)]
    ) in
  get_goals_aux [] term
;;

let affiche_context (gamma:context) : unit =
  List.iter
    (fun (x, ty) ->
      print_string x;
      print_string " : ";
      affiche_lam ty;
      print_newline ())
    (List.rev gamma)
;;

let affiche_goal (i, gamma, ty) : unit =
  print_newline ();
  print_string "Goal :";
  print_newline ();
  affiche_context gamma;
  print_string "----------------";
  print_newline ();
  affiche_lam ty;
  print_newline ()
;;

let numerote (term:lambdaterm) : lambdaterm =
  let next = ref 1 in
  let rec dfs term =
    match term with
    | Var _ | Type -> term
    | Goal (_, a) ->
        let i = !next in
        incr next;
        Goal (i, a)
    | Pi (x, a, b) -> Pi (x, a, b)
    | Func (x, a, b) -> Func (x, a, dfs b)
    | App (a, b) -> App (dfs a, dfs b)
  in
  dfs term
;;

let rec run_replace (term:lambdaterm) (func : lambdaterm -> lambdaterm) : lambdaterm =
  match term with
  | Var _ | Type -> term
  | Goal (i, a) -> func term
  | Pi (x, a, b) -> Pi (x, run_replace a func, b)
  | Func (x, a, b) -> Func (x, run_replace a func, run_replace b func)
  | App (a, b) -> App (run_replace a func, run_replace b func)
;;

let handle_tactic (i, gamma, _locgoal) term tactic = 
  match tactic with
  | Intro(x) ->
    let replace_goal goal = (match goal with
      | Goal(k, Pi("_", a, b)) when k=i -> Func(x, a, Goal(k, b))
      | _ -> goal
    ) in run_replace term replace_goal
  | Trivial ->
    let replace_goal goal = (match goal with
      | Goal(k, ty) when i=k -> 
        begin
          match List.find_opt (fun (_y, ty') -> alpha ty' ty) gamma with
          | Some (y, _ty') ->
              Var y
          | None ->
              goal
        end
      | _ -> goal
    ) in run_replace term replace_goal
  | Exact(t) ->
    let replace_goal goal = (match goal with
      | Goal(k, ty) when k=i ->
        begin
          if typecheck gamma t ty then
            t
          else
            goal
        end
      | _ -> goal
    ) in run_replace term replace_goal
;;

let interactive_step (term:lambdaterm) : lambdaterm option = 
  let first3 (x, _, _) = x in

  let term = numerote term in
  let mygoals = get_goals term in

  match mygoals with
    (*TODO : handle the end*)
    | [] -> 
      print_newline ();
      print_endline "No goals remaining.";
      print_endline "Witness of the proof :";
      print_endline (show_lambdaterm term);
      None
    | _ -> (
      let mygoal = List.hd mygoals in (*TODO : filter for goal 0*)
      affiche_goal mygoal;
      print_string "> ";
      let input = read_line () in
      let lexbuf = Lexing.from_string input in
      let tactic = Parser.tactic_main Lexer.token lexbuf in
      print_string "Tactique : ";
      print_string (show_tactic tactic);
      print_newline ();
      Some(handle_tactic mygoal term tactic)
    );
;;

let interactive (term:lambdaterm) : unit = 
  let current = ref term in
  let continue = ref true in

  while !continue do
    match interactive_step !current with
    | Some new_term ->
        current := new_term
    | None ->
        continue := false
  done
;;