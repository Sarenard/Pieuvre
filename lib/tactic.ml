open Expr
open Util

exception GoalRemaining;;
exception NoFocusedGoal;;

let handle_tactic goal term tactic 
  : (lambdaterm*bool) = (* (terme de retour, témoin de si on a fini) *) 
  match tactic with
  | Qed -> 
      if get_goals term = [] then
        (term, true)
      else
        raise GoalRemaining
  | _ when goal = None ->
      raise NoFocusedGoal
  | Intro(x) ->
    let (i, _gamma, _locgoal) = Option.get goal in
    let replace_goal goal = (match goal with
      | Goal(k, Pi("_", a, b)) when k=i -> Func(x, a, Goal(k, b))
      | _ -> goal
    ) in (run_replace term replace_goal, false)
  | Trivial ->
    let (i, gamma, _locgoal) = Option.get goal in
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
    ) in (run_replace term replace_goal, false)
  | Exact(t) ->
    let (i, gamma, _locgoal) = Option.get goal in
    let replace_goal goal = (match goal with
      | Goal(k, ty) when k=i ->
        begin
          try 
            typecheck gamma t ty;
            t
          with Type_error -> goal
        end
      | _ -> goal
    ) in (run_replace term replace_goal, false)
;;