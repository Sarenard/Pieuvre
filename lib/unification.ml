open! Expr
open Util

type lt = lambdaterm [@@deriving show]
type ty = lt [@@deriving show]

type sigma = (int, lt) Hashtbl.t
;;

let fresh_sigma () : sigma = Hashtbl.create 16
;;

let empty_sigma : sigma = fresh_sigma ()
;;

let pp_hashtbl pp_k pp_v fmt tbl =
  let first = ref true in
  Format.fprintf fmt "{";
  Hashtbl.iter (fun k v ->
    if !first then first := false else Format.fprintf fmt "; ";
    Format.fprintf fmt "%a: %a" pp_k k pp_v v
  ) tbl;
  Format.fprintf fmt "}"

let pp_sigma fmt sigma =
  pp_hashtbl Format.pp_print_int pp_lambdaterm fmt sigma

let show_sigma sigma =
  Format.asprintf "%a" pp_sigma sigma

exception UnificationError of lt*lt;;

let rec occurs_mvar (i : int) (term : lt) : bool =
  match term with
  | Mvar j -> i = j
  | Var _ | Type | Inductive _ -> false
  | Goal(_, t) -> occurs_mvar i t
  | App(t1, t2) -> occurs_mvar i t1 || occurs_mvar i t2
  | Pi(_, t1, t2)
  | Func(_, t1, t2) -> occurs_mvar i t1 || occurs_mvar i t2
  | Constructor(_, _, args) -> List.exists (occurs_mvar i) args
;;

let rec substitute_mvar (i : int) (replacement : lt) (term : lt) : lt =
  match term with
  | Mvar j -> if i = j then replacement else term
  | Var _ | Type | Inductive _ -> term
  | Goal(goal_id, t) -> Goal(goal_id, substitute_mvar i replacement t)
  | App(t1, t2) ->
    App(substitute_mvar i replacement t1, substitute_mvar i replacement t2)
  | Pi(x, t1, t2) ->
    Pi(x, substitute_mvar i replacement t1, substitute_mvar i replacement t2)
  | Func(x, t1, t2) ->
    Func(x, substitute_mvar i replacement t1, substitute_mvar i replacement t2)
  | Constructor(ind, cst, args) ->
    Constructor(ind, cst, List.map (substitute_mvar i replacement) args)
;;

let rec apply_sigma (sigma : sigma) (term : lt) : lt =
  match term with
  | Mvar i -> (
      match Hashtbl.find_opt sigma i with
      | Some t -> apply_sigma sigma t
      | None -> term
    )
  | Var _ | Type | Inductive _ -> term
  | Goal(goal_id, t) -> Goal(goal_id, apply_sigma sigma t)
  | App(t1, t2) -> App(apply_sigma sigma t1, apply_sigma sigma t2)
  | Pi(x, t1, t2) -> Pi(x, apply_sigma sigma t1, apply_sigma sigma t2)
  | Func(x, t1, t2) -> Func(x, apply_sigma sigma t1, apply_sigma sigma t2)
  | Constructor(ind, cst, args) ->
    Constructor(ind, cst, List.map (apply_sigma sigma) args)
;;

let instantiate_meta (sigma : sigma) (i : int) (term : lt) : sigma =
  let term = apply_sigma sigma term in
  match term with
  | Mvar j when i = j -> sigma
  | _ ->
    if occurs_mvar i term then
      raise (UnificationError(Mvar(i), term));
    Hashtbl.replace sigma i term;
    Hashtbl.iter (fun j t ->
      if i <> j then
        Hashtbl.replace sigma j (substitute_mvar i term t)
    ) sigma;
    sigma
;;

let extend_context (ctx : context) (x : string) (ty : lt) : context = {
  gamma = (x, ty) :: ctx.gamma;
  values = ctx.values;
  inductive_types = ctx.inductive_types;
}
;;

(*
based on https://www.cambridge.org/core/services/aop-cambridge-core/content/view/19A095CA0645F89A772B7E2B7B3D92B2/S0956796817000028a.pdf/a-comprehensible-guide-to-a-new-unifier-for-cic-including-universe-polymorphism-and-overloading.pdf
but for now its too complicated
we go back to an easier unification algorithm
*)
(*TODO : add reductions*)
let rec unify (sigma0:sigma) (ctx:context) (e1:lt) (e2:lt) : sigma =
  let e1 = apply_sigma sigma0 e1 in
  let e2 = apply_sigma sigma0 e2 in
  match (e1, e2) with
  (*TYPE-SAME*)
  | (Type, Type) -> sigma0
  (*VAR-SAME*)
  (*RIGID-SAME*) (*we dont use E right now*)
  | (Var(x), Var(y)) ->
    if x <> y then raise (UnificationError(e1, e2));
    sigma0
  (*PROD-SAME and LAM-SAME*)
  | (Pi(x, t1, t2), Pi(y, u1, u2))
  | (Func(x, t1, t2), Func(y, u1, u2)) ->
    (*we \alpha-rename both*)
    let t1spoiled = unfresh t1 in
    let t2spoiled = unfresh t2 in
    let u1spoiled = unfresh u1 in
    let u2spoiled = unfresh u2 in
    let contextbound = List.map fst ctx.gamma in
    let spoiled = t1spoiled @ t2spoiled @ u1spoiled @ u2spoiled @ contextbound in
    let fresh = get_fresh "unif" spoiled in
    let x' = Var(fresh) in
    let t2' = replace t2 x x' in
    let u2' = replace u2 y x' in
    (*we compute the new mcontext*)
    let sigma1 = unify sigma0 ctx t1 u1 in
    let sigma2 = unify sigma1 (extend_context ctx fresh t1) t2' u2' in
    sigma2
  | Mvar i, Mvar j when i = j ->
    sigma0
  | Mvar i, t ->
    instantiate_meta sigma0 i t
  | t, Mvar i ->
    instantiate_meta sigma0 i t
  | Inductive i, Inductive j when i = j ->
    sigma0
  | Constructor(i1, c1, args1), Constructor(i2, c2, args2)
    when i1 = i2 && c1 = c2 && List.length args1 = List.length args2 ->
    unify_pairs sigma0 ctx args1 args2
  | Goal(_, t1), Goal(_, t2) ->
    unify sigma0 ctx t1 t2
  | App(f1, a1), App(f2, a2) ->
    let sigma1 = unify sigma0 ctx f1 f2 in
    unify sigma1 ctx a1 a2
  | _, _ ->
    raise (UnificationError(e1, e2))
and unify_pairs (sigma : sigma) (ctx : context) (list1 : lt list) (list2 : lt list) : sigma =
  match list1, list2 with
  | [], [] -> sigma
  | t1 :: q1, t2 :: q2 ->
    let sigma1 = unify sigma ctx t1 t2 in
    unify_pairs sigma1 ctx q1 q2
  | _, _ -> raise (UnificationError(delinearize_list list1, delinearize_list list2))
;;

let test menv ctx e1 e2 = 
  try 
    let new_sigma = unify menv ctx e1 e2 in
    print_endline ("( "^(show_lt e1) ^ " ~ " ^ (show_lt e2) ^ " ) = " ^ show_sigma new_sigma);
  with
  | UnificationError(e1, e2) ->
    print_endline ("Failed to unify " ^ show_lt e1 ^ " and " ^ show_lt e2);
  | Failure msg ->
    print_endline ("Failure while unifying " ^ show_lt e1 ^ " and " ^ show_lt e2 ^ ": " ^ msg);
  ;
;;

(*for tests*)
let unify_run () = 
  test (fresh_sigma ()) empty_env Type Type; 
  test (fresh_sigma ()) empty_env (Var("x")) (Var("y")); 
  test (fresh_sigma ()) empty_env (Var("x")) (Var("x")); 
  test (fresh_sigma ()) empty_env
    (Pi("x", Type, Var("x")))
    (Pi("y", Type, Var("y")));
  test (fresh_sigma ()) empty_env
    (Pi("x", Type, Type))
    (Pi("y", Type, Type));
  test (fresh_sigma ()) empty_env
    (Pi("x", Type, Var("x")))
    (Pi("y", Type, Var("z")));
  test (fresh_sigma ()) empty_env
    (Func("x", Type, Var("x")))
    (Func("y", Type, Var("y")));
  test (fresh_sigma ()) empty_env
    (Func("x", Type, Type))
    (Func("y", Type, Type));
  test (fresh_sigma ()) empty_env
    (Func("x", Type, Var("x")))
    (Func("y", Type, Var("z")));
  test (fresh_sigma ()) empty_env
    (App(App(App(Var("f"), Var("x1")), Var("x2")), Var("x3")))
    (App(App(App(Var("f"), Var("x1")), Var("x2")), Var("x4")));
  test (fresh_sigma ()) empty_env
    (App(App(App(Var("f"), Var("x1")), Var("x2")), Var("x3")))
    (App(App(App(Var("f"), Var("x1")), Var("x2")), Var("x3")));
  test (fresh_sigma ()) empty_env
    (App(App(App(Var("f"), Var("x1")), Var("x2")), Var("x3")))
    (App(App(Var("f"), Var("x1")), Var("x2")));
  test (fresh_sigma ()) empty_env (Mvar(0)) (Mvar(1));
  test (fresh_sigma ()) empty_env (Mvar(2)) (App(Var("f"), Var("x")));
  test (fresh_sigma ()) empty_env
    (App(Mvar(0), Mvar(0)))
    (App(Var("x"), Var("x")));
  test (fresh_sigma ()) empty_env
    (App(Mvar(0), Mvar(0)))
    (App(Var("x"), Var("y")));
  test (fresh_sigma ()) empty_env
    (App(
      App(Mvar(0), App(Mvar(1), Mvar(2))),
      App(Mvar(1), App(Mvar(2), Var("z")))
    ))
    (App(
      App(Var("f"), App(Var("g"), Var("x"))),
      App(Var("g"), App(Var("x"), Var("z")))
    ));
;;
