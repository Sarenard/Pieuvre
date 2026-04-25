open Expr

let parse_type (ty:string) : lambdaterm = Parser.main_term Lexer.token (Lexing.from_string ty);; 
let parse_tactic (ty:string) : tactic = Parser.main_tactic Lexer.token (Lexing.from_string ty);; 
let parse_statements (ty:string) : statement list = Parser.main_statements Lexer.token (Lexing.from_string ty);; 

let get_goals (gamma:context) (term:lambdaterm) =
  let rec get_goals_aux (gamma:context) (term:lambdaterm) : (int * context * lambdaterm) list = 
    let (gamma_var, gamma_ind) = gamma in (
      match term with
      | Var(_x) -> []
      | Type -> []
      | Pi(x, a, b) -> 
        let new_env = (((x, a)::gamma_var), gamma_ind) in
        (get_goals_aux gamma a)@(get_goals_aux new_env b) 
      | Func(x, a, b) -> 
        let new_env = (((x, a)::gamma_var), gamma_ind) in
        get_goals_aux new_env b
      | App(a, b) -> (get_goals_aux gamma a)@(get_goals_aux gamma b)
      | Goal(i, a) -> [(i, gamma, a)]
      | Inductive(_) -> []
      | Constructor(_, _, _) -> []
    ) in get_goals_aux gamma term
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
    | Pi (x, a, b) -> Pi (x, dfs a, dfs b)
    | Func (x, a, b) -> Func (x, dfs a, dfs b)
    | App (a, b) -> App (dfs a, dfs b)
    | Inductive(_) -> term
    | Constructor(_, _, _) -> term
  in
  dfs term
;;

let rec run_replace (term:lambdaterm) (func : lambdaterm -> lambdaterm) : lambdaterm =
  match term with
  | Var _ | Type -> term
  | Goal (_i, _a) -> func term
  | Pi (x, a, b) -> Pi (x, run_replace a func, run_replace b func)
  | Func (x, a, b) -> Func (x, run_replace a func, run_replace b func)
  | App (a, b) -> App (run_replace a func, run_replace b func)
  | Inductive(_) -> term
  | Constructor(i, j, lst) -> Constructor(i, j, List.map (fun t -> run_replace t func) lst)
;;

let show_list show xs =
  let contents = List.map show xs |> String.concat "; " in
  "[" ^ contents ^ "]"
;;
