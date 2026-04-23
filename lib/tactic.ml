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
  | Intro(x) -> let replace_goal goal = (match goal with
      (*TODO : fix this with dependant types*)
      | Goal(k, Pi("_", a, b)) when k=i -> Func(x, a, Goal(k, b))
      | _ -> goal
    ) in run_replace term replace_goal
  | Trivial -> let replace_goal goal = (match goal with
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
  | Exact(t) -> let replace_goal goal = (match goal with
      | Goal(k, ty) when k=i ->
        begin
          try 
            typecheck big_gamma t ty;
            t
          with Type_error -> goal
        end
      | _ -> goal
    ) in run_replace term replace_goal
  | Apply(x) -> let replace_goal goal =
      match goal with
      | Goal(k, ty) when k = i -> (
        match List.find_opt (fun (y, _) -> x = y) big_gamma with
        | Some (_, fty) ->
          let rec collect_args args fty =
            let fty = reduce fty in
            match fty with
            | _ when equiv fty ty -> Some (List.rev args)
            | Pi(arg, a, b) ->
              (*we put back numbers after so its okay to put them as 0*)
              let new_goal = Goal(0, a) in
              (*Dependant types so we need to replace*)
              (*TODO : do this but properly with unification*)
              collect_args (new_goal :: args) (replace b arg new_goal)
            | _ -> None
          in (
            match collect_args [] fty with
            | Some [] -> Var x
            | Some args -> List.fold_left (fun acc arg -> App(acc, arg)) (Var x) args
            | None -> goal
          )
        | None -> goal
      )
      | _ -> goal
    in run_replace term replace_goal
;;
