open Expr

let parse_type (ty:string) : lambdaterm = Parser.main_term Lexer.token (Lexing.from_string ty);; 
let parse_tactic (ty:string) : tactic = Parser.main_tactic Lexer.token (Lexing.from_string ty);; 
let parse_statements (ty:string) : statement list = Parser.main_statements Lexer.token (Lexing.from_string ty);; 

let get_goals (gamma:context) (term:lambdaterm) =
  let rec get_goals_aux (gamma:context) (term:lambdaterm) : (int * context * lambdaterm) list = 
    let gamma_var = gamma.gamma in
    let gamma_ind = gamma.inductive_types in
    let gamma_val = gamma.values in (
      match term with
      | Var(_x) -> []
      | Type -> []
      | Pi(x, a, b) -> 
        let new_env = { gamma = (x, a) :: gamma_var; inductive_types = gamma_ind ; values = gamma_val} in
        (get_goals_aux gamma a)@(get_goals_aux new_env b) 
      | Func(x, a, b) -> 
        let new_env = { gamma = (x, a) :: gamma_var; inductive_types = gamma_ind ; values = gamma_val} in
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
    | Constructor(i, j, args) -> Constructor(i, j, List.map dfs args)
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

let get_new_name used = 
  let var_name = get_fresh "x" (!used) in
  used := var_name::(!used);
  var_name
;;

let rec listify used = function
  | Pi(x, a, b) -> 
    let new_var = get_new_name used in
    (new_var, a)::(listify used (replace b x (Var(new_var))))
  | _ -> [];
;;

let rec listify_app used = function
  | App(a, Var(x)) -> 
    x::(listify_app used a)
  | Var(x) -> [];
  | _ -> [];
;;

let rec last_arrow = function
  | Pi(x, a, b) -> last_arrow b
  | ty -> ty
;;

let rec last_app = function
  | App(a, b) -> last_app a
  | ty -> ty
;;

let rec last_app_change x = function
  | App(a, b) -> App(last_app_change x a, b)
  | ty -> x
;;

let rec instantiate_return_type term args =
  match term, args with
  | Pi(x, _, body), (name, _) :: rest ->
    instantiate_return_type (replace body x (Var(name))) rest
  | ty, [] -> ty
  | ty, _ -> ty
;;

(*
RECURSOR OF FIN
Check fin_ind.
T_ind : 
forall P : forall n : nat, T n -> Prop,
P 0 a ->
(forall (n m : nat) (t : T n) (t0 : T m),
P n t -> P m t0 -> P (n + m) (b n m t t0)) ->
forall (n : nat) (t : T n), P n t
*)

let compute_recursor name arity constructors = 
  (*setup of the names*)
  let used_vars = ref [] in
  used_vars := name::!used_vars;
  let add_constr_name constrs =
    let rec aux = function
    | (cname, _ty)::xs -> 
      used_vars := cname::!used_vars;
      aux xs;
      | [] -> ()
    in aux constrs;
  in add_constr_name constructors;

  let prop_name = get_fresh "P" (!used_vars) in
  used_vars := prop_name::!used_vars;
  
  let arity_listified = listify used_vars arity in
  (*print_endline (show_list (fun (x, a) -> "(" ^ x ^ ", " ^ affiche_lam a ^ ")") arity_listified);*)

  let new_name = get_new_name used_vars in 
  let conclusion = (
    List.fold_left 
    (fun acc (name, ty) -> (Pi(name, ty, acc)))
    (Pi(
      new_name,
      (
        List.fold_left
        (fun acc (name, ty) -> App(acc, Var(name)))
        (Var(name))
        (arity_listified)
      ),
      App((
        List.fold_left
        (fun acc (name, ty) -> App(acc, Var(name)))
        (Var(prop_name))
        arity_listified
      ), Var(new_name))
    ))
    (List.rev arity_listified) 
  ) in

  let prop_type = (
    (
      List.fold_left 
      (fun acc (name, ty) -> (Pi(name, ty, acc)))
      (Pi(
        "_",
        List.fold_left
        (fun acc (name, ty) -> App(acc, Var(name)))
        (Var(name))
        (arity_listified),
        Type
      ))
      (List.rev arity_listified) 
    )
  ) in

  let handle_constructor (cname, constructor) = (
    let listified = listify used_vars constructor in
    (*print_endline (show_list (fun (x, a) -> "(" ^ x ^ ", " ^ affiche_lam a ^ ")") listified);*)
    let filtered = List.filter (fun (x, a) -> (last_app a) = Var(name)) listified in
    (*print_endline (show_list (fun (x, a) -> "(" ^ x ^ ", " ^ affiche_lam a ^ ")") filtered);*)
    let instantiated_return = instantiate_return_type constructor listified in
    let p_call = (
      App(
        last_app_change (Var(prop_name)) instantiated_return,
        List.fold_left
        (fun acc (name, ty) -> App(acc, Var(name)))
        (Var(cname))
        (listified)
      )
    ) in
    List.fold_left 
    (fun acc (name, ty) -> (Pi(name, ty, acc)))
    (*This is the Pn in Pn -> Pn+1 inside of nats rec*)
    (
      List.fold_left
      (fun acc (name, ty) ->
        Pi("_", App(last_app_change (Var(prop_name)) ty, Var(name)), acc)
      )
      p_call
      (List.rev filtered)
    )
    (List.rev listified) 
  ) in
  let body = 
    List.fold_left
    (fun acc constr -> Pi("_", handle_constructor constr, acc))
    conclusion
    (List.rev constructors)
  in

  Pi(
    prop_name,
    prop_type,
    body
  )
;;
