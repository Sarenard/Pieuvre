open Expr

let parse_type (ty:string) : lambdaterm = Parser.main_term Lexer.token (Lexing.from_string ty);; 
let parse_tactic (ty:string) : tactic = Parser.main_tactic Lexer.token (Lexing.from_string ty);; 
let parse_statements (ty:string) : statement list = Parser.main_statements Lexer.token (Lexing.from_string ty);; 

(*
Gets a list of the goals
*)
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
      | Constructor(_, _, lst) -> List.concat_map (get_goals_aux gamma) lst
    ) in get_goals_aux gamma term
;;

(*
numbers every goal
*)
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

(*
An helper function to run a func on every goal : searching the one we will replace with a tactic
*)
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

(*
Transforms a series of Pi-types into a list
(A:Type) -> (x:A) -> (y:A) -> Type
into
[(A:Type), (x:A), (y:A)]
*)
let rec listify used = function
  | Pi(x, a, b) -> 
    let new_var = get_new_name used in
    (new_var, a)::(listify used (replace b x (Var(new_var))))
  | _ -> [];
;;

(*
Transforms a series of applications into a list
Ignores the first, transforms
f x y
into
[y; x]
*)
let rec listify_app used = function
  | App(a, Var(x)) -> 
    x::(listify_app used a)
  | _ -> [];
;;

(*
Gets the last item of a series of Pi-types
(A:Type) -> (x:A) -> (y:A)
into
(y:A)
*)
let rec last_arrow = function
  | Pi(x, a, b) -> last_arrow b
  | ty -> ty
;;

(*
Gets the last item of a series of apps
f x y
into
f
*)
let rec last_app = function
  | App(a, b) -> last_app a
  | ty -> ty
;;

(*
Replaces the last item of a series of apps
last_app_change <term> (f x y)
into
<term> x y
*)
let rec last_app_change x = function
  | App(a, b) -> App(last_app_change x a, b)
  | ty -> x
;;

(*
Instantiate a Pi-typed term with a sequence of arguments.
If the term is
(A:Type) -> (x:A) -> eq A x x
and the arguments are
[(B:Type); (k:B)]
then this returns
eq B k k
*)
let rec instantiate_return_type term args =
  match term, args with
  | Pi(x, _, body), (name, _) :: rest ->
    instantiate_return_type (replace body x (Var(name))) rest
  | ty, [] -> ty
  | ty, _ -> ty
;;


(*
Computes the recursor of an inductive type
If the inductive type is
Inductive T : Arity :=
  | Cons_1 : Signature_1 -> T <args_1>
  ...
  | Cons_n : Signature_n -> T <args_n>
Then the recursor is* of the form
(\*approximately of the form, this is intended to give an idea, not the full definition)
forall P : ~Arity -> Type,
(forall <Signature_1>, (P <args> when things in Signature_1 use T) -> P <args> (Cons_1 <args_1)) ->
...
(forall <Signature_n>, (P <args> when things in Signature_n use T) -> P <args> (Cons_n <args_n)) ->
forall <Arity>, P <args>
Some examples :
for nat :
(forall P : Nat -> Type, P 0 -> (forall n : N, P n -> P (S n)) -> forall n:N, P n)
for eq:
(forall P : forall (A : Type) (x y : A), eq A x y -> Type,
  (forall (A : Type) (x : A), P A x x (refl A x)) ->
forall (A : Type) (x y : A) (e : eq A x y), P A x y e)
*)
let compute_recursor name arity constructors = 
  let debug = false in (*For debug purposes,*)
  (*setup of the spoiled names*)
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
  if debug then (print_endline (show_list (fun (x, a) -> "(" ^ x ^ ", " ^ affiche_lam a ^ ")") arity_listified););

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
    if debug then (print_endline (show_list (fun (x, a) -> "(" ^ x ^ ", " ^ affiche_lam a ^ ")") listified););
    let filtered = List.filter (fun (x, a) -> (last_app a) = Var(name)) listified in
    if debug then (print_endline (show_list (fun (x, a) -> "(" ^ x ^ ", " ^ affiche_lam a ^ ")") filtered););
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
    (*This is the Pn in Pn -> Pn+1 inside of nats recursor, we need to suppose P of the inductive quantified elements*)
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
