open Expr
open Util

(*
gamma : context of the goal
gamma' : context of the theorem
*)
let handle_tactic (i, (gamma:context), _locgoal) (gamma':context) term tactic : lambdaterm =  
  let (gamma_var, gamma_ind) = gamma in
  let (gamma_var', gamma_ind') = gamma' in
  let big_gamma = (gamma_var@gamma_var', gamma_ind@gamma_ind') in
  let (gamma_var, gamma_ind) = big_gamma in
  match tactic with
  | Intro(x) -> (
    match List.assoc_opt x gamma_var with
    | Some(_) -> failwith ("Cannot intro here, variable " ^ x ^ " already taken")
    | None -> (
      let replace_goal goal = (match goal with
        | Goal(k, Pi("_", a, b)) when k=i -> Func(x, a, Goal(k, b))
        (*dependant*)
        | Goal(k, Pi(var, a, b)) when k=i -> Func(x, a, Goal(k, replace b var (Var x)))
        | _ -> goal
      ) in run_replace term replace_goal
    )
  )
  (*TODO : faire ça avec de l'unification*)
  | Trivial -> let replace_goal goal = (match goal with
      | Goal(k, ty) when i=k -> 
        begin
          match List.find_opt (fun (_y, ty') -> equiv ty' ty) gamma_var with
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
  (*TODO : add apply but for constructors too*)
  | Apply(x) -> let replace_goal goal =
      match goal with
      | Goal(k, ty) when k = i -> (
        match List.find_opt (fun (y, _) -> x = y) gamma_var with
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
              (* Zoe said :
                dans une implémentation propre de apply tu remplaces le replace par une unification
                l'unification te yield une solution
                ça t'a unifié ton goal et les hypothèses du apply
                et t'as juste à introduire les hypothèses unifiées
              *)
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
