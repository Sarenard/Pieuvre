open! Expr
open Util

type lt = lambdaterm [@@deriving show]
type ty = lt [@@deriving show]

type mcontext = {
  values : (int, lt) Hashtbl.t;
  types : (int, lt) Hashtbl.t;
}
;;

let fresh_mcontext () : mcontext = {
  values = Hashtbl.create 16;
  types = Hashtbl.create 16;
}
;;

let empty_mcontext : mcontext = fresh_mcontext ()
;;

type lcontext = (string * lt) list
[@@deriving show]
;;

(*WARNING : NOT USED RIGHT NOW*)
type globalenv = (string * lt) list
[@@deriving show]
;;

let pp_hashtbl pp_k pp_v fmt tbl =
  let first = ref true in
  Format.fprintf fmt "{";
  Hashtbl.iter (fun k v ->
    if !first then first := false else Format.fprintf fmt "; ";
    Format.fprintf fmt "%a: %a" pp_k k pp_v v
  ) tbl;
  Format.fprintf fmt "}"

let pp_mcontext fmt ctx =
  Format.fprintf fmt "{ values = %a; types = %a }"
    (pp_hashtbl Format.pp_print_int pp_lambdaterm) ctx.values
    (pp_hashtbl Format.pp_print_int pp_lambdaterm) ctx.types

let show_mcontext ctx =
  Format.asprintf "%a" pp_mcontext ctx

(*
Returns if lt1 \delta\Sigma reduces in lt2 in the context mctx
*)    
let delta_sigma_reduce_t (lt1:lt) (lt2:lt) (mctx : mcontext) : bool =
  match lt1 with
  | Mvar(i) -> has_binding (mctx.values) i lt2
  | _ -> failwith "Wrong left argument for delta_sigma_reduce"
;;

(*
Returns if lt1 \delta\Sigma^weak reduces in lt2
*)
let rec delta_sigma_reduce_weak_t (lt1:lt) (lt2:lt) : bool =
  match (lt1, lt2) with
  | (t, t') when 
    delta_sigma_reduce_t t t' empty_mcontext 
    -> true
  | (App(t, u1), App(t', u2)) when 
    u1 = u2 && delta_sigma_reduce_weak_t t t' 
    -> true
  | _ -> false
;;

(*
Computes the \delta\Sigma^weak reduction of lt1 in the context mctx
*)
let delta_sigma_reduce (mctx : mcontext) (lt1 : lt) : lt option =
  match lt1 with
  | Mvar i -> Hashtbl.find_opt mctx.values i
  | _ -> None
;;

(*
Computes the \delta\Sigma^weak reduction of lt1
*)
let rec delta_sigma_reduce_weak (mctx : mcontext) (lt1:lt) : lt option =
  match lt1 with
  | App(t, u) -> 
    (match delta_sigma_reduce_weak mctx t with
    | Some(t') -> Some(App(t', u))
    | None -> None)
  | _ -> delta_sigma_reduce mctx lt1
;;

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

let instantiate_meta (sigma : mcontext) (i : int) (term : lt) : mcontext =
  match term with
  | Mvar j when i = j -> sigma
  | _ ->
    if occurs_mvar i term then
      raise (UnificationError(Mvar(i), term));
    Hashtbl.replace sigma.values i term;
    sigma
;;

(*
based on https://www.cambridge.org/core/services/aop-cambridge-core/content/view/19A095CA0645F89A772B7E2B7B3D92B2/S0956796817000028a.pdf/a-comprehensible-guide-to-a-new-unifier-for-cic-including-universe-polymorphism-and-overloading.pdf
but for now its too complicated
we go back to an easier unification algorithm
*)
let rec unify (sigma0:mcontext) (lenv:lcontext) (e1:lt) (e2:lt) : mcontext =
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
    let contextbound = List.map (fun (a, b) -> a) lenv in
    let spoiled = t1spoiled @ t2spoiled @ u1spoiled @ u2spoiled @ contextbound in
    let fresh = get_fresh "unif" spoiled in
    let x' = Var(fresh) in
    let t2' = replace t2 x x' in
    let u2' = replace u2 y x' in
    (*we compute the new mcontext*)
    let sigma1 = unify sigma0 lenv t1 u1 in
    let sigma2 = unify sigma1 ((fresh, t1)::lenv) t2' u2' in
    sigma2
  | Mvar i, Mvar j when i = j ->
    sigma0
  | Mvar i, t ->
    instantiate_meta sigma0 i t
  | t, Mvar i ->
    instantiate_meta sigma0 i t
  | App(f1, a1), App(f2, a2) ->
    let sigma1 = unify sigma0 lenv f1 f2 in
    unify sigma1 lenv a1 a2
  | _, _ ->
    raise (UnificationError(e1, e2))
;;

let test menv lenv e1 e2 = 
  try 
    let newctx = unify menv lenv e1 e2 in
    print_endline ("( "^(show_lt e1) ^ " ~ " ^ (show_lt e2) ^ " ) = " ^ show_mcontext newctx);
  with
  | UnificationError(e1, e2) ->
    print_endline ("Failed to unify " ^ show_lt e1 ^ " and " ^ show_lt e2);
  | Failure msg ->
    print_endline ("Failure while unifying " ^ show_lt e1 ^ " and " ^ show_lt e2 ^ ": " ^ msg);
  ;
;;

(*for tests*)
let unify_run () = 
  test (fresh_mcontext ()) [] Type Type; 
  test (fresh_mcontext ()) [] (Var("x")) (Var("y")); 
  test (fresh_mcontext ()) [] (Var("x")) (Var("x")); 
  test (fresh_mcontext ()) []
    (Pi("x", Type, Var("x")))
    (Pi("y", Type, Var("y")));
  test (fresh_mcontext ()) []
    (Pi("x", Type, Type))
    (Pi("y", Type, Type));
  test (fresh_mcontext ()) []
    (Pi("x", Type, Var("x")))
    (Pi("y", Type, Var("z")));
  test (fresh_mcontext ()) []
    (Func("x", Type, Var("x")))
    (Func("y", Type, Var("y")));
  test (fresh_mcontext ()) []
    (Func("x", Type, Type))
    (Func("y", Type, Type));
  test (fresh_mcontext ()) []
    (Func("x", Type, Var("x")))
    (Func("y", Type, Var("z")));
  test (fresh_mcontext ()) []
    (App(App(App(Var("f"), Var("x1")), Var("x2")), Var("x3")))
    (App(App(App(Var("f"), Var("x1")), Var("x2")), Var("x4")));
  test (fresh_mcontext ()) []
    (App(App(App(Var("f"), Var("x1")), Var("x2")), Var("x3")))
    (App(App(App(Var("f"), Var("x1")), Var("x2")), Var("x3")));
  test (fresh_mcontext ()) []
    (App(App(App(Var("f"), Var("x1")), Var("x2")), Var("x3")))
    (App(App(Var("f"), Var("x1")), Var("x2")));
  test (fresh_mcontext ()) [] (Mvar(0)) (Mvar(1));
  test (fresh_mcontext ()) [] (Mvar(2)) (App(Var("f"), Var("x")));
;;
