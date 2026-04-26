open! Expr
open Util

type lt = lambdaterm [@@deriving show]
type ty = lt [@@deriving show]

type mcontext = {
  values : (int, lt) Hashtbl.t;
  types : (int, lt) Hashtbl.t;
}
;;

let empty_mcontext : mcontext = {
  values = Hashtbl.create 16;
  types = Hashtbl.create 16;
}
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
  match lt2 with
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

let rec unify (sigma0:mcontext) (lenv:lcontext) (e1:lt) (e2:lt) : mcontext =
  match (e1, e2) with
  (*TYPE-SAME*)
  | (Type, Type) -> sigma0
  (*VAR-SAME*)
  (*RIGID-SAME*) (*we dont use E right now, we*)
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
  | e1, e2 ->
    let head1, tail1 = uncons (linearize e1) in
    let head2, tail2 = uncons (linearize e2) in

    (*We try to META-delta(L/R) reduce*)
    match delta_sigma_reduce_weak sigma0 head1, delta_sigma_reduce_weak sigma0 head2 with
      | Some head1, Some head2 ->
        unify sigma0 lenv (delinearize head1 tail1) (delinearize head2 tail2)
      | Some head1, None ->
        unify sigma0 lenv (delinearize head1 tail1) e2
      | None, Some head2 ->
        unify sigma0 lenv e1 (delinearize head2 tail2)
      | None, None ->
        (*META-SAME or META-INST(R/L) or app_fo depending*)
        match head1, head2 with
        (*META-SAME*)
        | Mvar i, Mvar j when i = j ->
          failwith "TODO";
        (*META-INST-L*)
        | Mvar i, t ->
          failwith "TODO";
        (*META-INST-R*)
        | t, Mvar i ->
          failwith "TODO";
        (*APP-FO*)
        | _, _ ->
          let sigma1 = unify sigma0 lenv head1 head2 in
          (*We need to compress the combs so they have the same length*)
          failwith "TODO";
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
  test empty_mcontext [] Type Type; 
  test empty_mcontext [] (Var("x")) (Var("y")); 
  test empty_mcontext [] (Var("x")) (Var("x")); 
  test empty_mcontext []
    (Pi("x", Type, Var("x")))
    (Pi("y", Type, Var("y")));
  test empty_mcontext []
    (Pi("x", Type, Type))
    (Pi("y", Type, Type));
  test empty_mcontext []
    (Pi("x", Type, Var("x")))
    (Pi("y", Type, Var("z")));
  test empty_mcontext []
    (Func("x", Type, Var("x")))
    (Func("y", Type, Var("y")));
  test empty_mcontext []
    (Func("x", Type, Type))
    (Func("y", Type, Type));
  test empty_mcontext []
    (Func("x", Type, Var("x")))
    (Func("y", Type, Var("z")));
  test empty_mcontext []
    (App(App(App(Var("f"), Var("x1")), Var("x2")), Var("x3")))
    (App(App(App(Var("f"), Var("x1")), Var("x2")), Var("x4")));
  test empty_mcontext []
    (App(App(App(Var("f"), Var("x1")), Var("x2")), Var("x3")))
    (App(App(App(Var("f"), Var("x1")), Var("x2")), Var("x3")));
;;
