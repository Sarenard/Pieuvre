open Expr
open Util

(*
gamma : context of the goal
gamma' : context of the theorem
*)
let handle_tactic (i, gamma, _locgoal) (gamma':context) term tactic : lambdaterm =  
  let big_gamma = (gamma@gamma') in
  match tactic with
  (*TODO : intro should fail if x already in the context*)
  | Intro(x) ->
    let replace_goal goal = (match goal with
      | Goal(k, Pi("_", a, b)) when k=i -> Func(x, a, Goal(k, b))
      | _ -> goal
    ) in run_replace term replace_goal
  | Trivial ->
    let replace_goal goal = (match goal with
      | Goal(k, ty) when i=k -> 
        begin
          match List.find_opt (fun (_y, ty') -> alpha ty' ty) big_gamma with
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
          try 
            typecheck big_gamma t ty;
            t
          with Type_error -> goal
        end
      | _ -> goal
    ) in run_replace term replace_goal
;;