open Expr
open Util
open Unification

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
          let next_mvar = ref 0 in
          let fresh_mvar () =
            let id = !next_mvar in
            incr next_mvar;
            id
          in
          let sigma = fresh_sigma () in
          let meta_types : (int, lambdaterm) Hashtbl.t = Hashtbl.create 16 in
          (*does the substitution*)
          let rec materialize_term tm =
            match apply_sigma sigma tm with
            | Mvar j -> (
              match Hashtbl.find_opt meta_types j with
              | Some meta_ty -> Goal(0, materialize_term meta_ty)
              | None -> Mvar j
            )
            | Var _ | Type | Inductive _ as tm -> tm
            | Goal(goal_id, tm) -> Goal(goal_id, materialize_term tm)
            | App(t1, t2) -> App(materialize_term t1, materialize_term t2)
            | Pi(arg, a, b) -> Pi(arg, materialize_term a, materialize_term b)
            | Func(arg, a, b) -> Func(arg, materialize_term a, materialize_term b)
            | Constructor(ind, cst, args) ->
              Constructor(ind, cst, List.map materialize_term args)
          in
          let rec collect_args args fty =
            let fty = reduce big_gamma (apply_sigma sigma fty) in
            try
              let sigma' = unify sigma big_gamma fty ty in
              Some (sigma', List.rev args)
            with
            | UnificationError _ -> (
              match fty with
              | Pi(arg, a, b) ->
                let meta_id = fresh_mvar () in
                let meta = Mvar meta_id in
                Hashtbl.replace meta_types meta_id a;
                collect_args (meta :: args) (replace b arg meta)
              | _ -> None
            )
          in (
            match collect_args [] fty with
            | Some (_, []) -> Var x
            | Some (_, args) ->
              List.fold_left
                (fun acc arg -> App(acc, materialize_term arg))
                (Var x)
                args
            | None -> goal
          )
        | None -> goal
      )
      | _ -> goal
    in run_replace term replace_goal
    | Cut(x) -> let replace_goal goal = 
      match goal with
      | Goal(k, ty) when k = i -> App(Goal(k, Pi("_", x, ty)), Goal(0, x))
      | _ -> goal
    in run_replace term replace_goal
;;
