open Expr

let parse_type (ty:string) : lambdaterm = Parser.main Lexer.token (Lexing.from_string ty);; 
let parse_tactic (ty:string) : tactic = Parser.tactic_main Lexer.token (Lexing.from_string ty);; 

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
  get_goals_aux empty_env term
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

