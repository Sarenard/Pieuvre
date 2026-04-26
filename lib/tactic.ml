open Expr
open Util

(*
This is the function that handles tactics
gamma : context of the goal
gamma' : context of the theorem
*)
let handle_tactic (i, (gamma:context), _locgoal) (gamma':context) term tactic : lambdaterm =  
  let gamma_var = gamma.gamma in
  let gamma_var' = gamma'.gamma in
  let big_gamma = {
    gamma = gamma_var @ gamma_var';
    inductive_types = gamma.inductive_types @ gamma'.inductive_types;
    values = gamma.values @ gamma'.values;
  } in
  let gamma_var = big_gamma.gamma in
  match tactic with
  | Intro(x) -> (
    match List.assoc_opt x gamma_var with
    | Some(_) -> failwith ("Cannot intro here, variable " ^ x ^ " already taken")
    | None -> (
      let replace_goal goal = (match goal with
        (*non dependant introduction*)
        | Goal(k, Pi("_", a, b)) when k=i -> Func(x, a, Goal(k, b))
        (*dependant introduction*)
        | Goal(k, Pi(var, a, b)) when k=i -> Func(x, a, Goal(k, replace b var (Var x)))
        | _ -> goal
      ) in run_replace term replace_goal
    )
  )
  | Trivial -> let replace_goal goal = (match goal with
      | Goal(k, ty) when i=k -> 
        begin
          match List.find_opt (fun (_y, ty') -> equiv big_gamma ty' ty) gamma_var with
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
            (*TODO : remove this because we have a better system of error handling !*)
            let debug = false in
            if debug then (
              print_endline ("t = " ^ (affiche_lam t));
              print_endline ("reduce t = " ^ (affiche_lam (reduce gamma t)));
              print_endline ("ty = " ^ (affiche_lam ty));
              print_endline ("infered t = " ^ (affiche_lam (infer gamma t)));
            );
            typecheck big_gamma t ty;
            t
          with Type_error -> goal
        end
      | _ -> goal
    ) in run_replace term replace_goal
  | Apply(x) -> let replace_goal goal =
      match goal with
      | Goal(k, ty) when k = i -> (
        match List.find_opt (fun (y, _) -> x = y) gamma_var with
        | Some (_, fty) ->
          let rec collect_args args fty =
            let fty = reduce big_gamma fty in
            match fty with
            | _ when equiv big_gamma fty ty -> Some (List.rev args)
            | Pi(arg, a, b) ->
              (*we put back numbers after so its okay to put them as 0 for now*)
              let new_goal = Goal(0, a) in
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
