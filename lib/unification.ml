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
let delta_sigma_reduce (lt1 : lt) (mctx : mcontext) : lt =
  match lt1 with
  | Mvar i ->
    (match Hashtbl.find_opt mctx.values i with
    | Some v -> v
    | None -> lt1)
  | _ -> lt1
;;

(*
Computes the \delta\Sigma^weak reduction of lt1
*)
let rec delta_sigma_reduce_weak (lt1:lt) : lt =
  match lt1 with
  | App(t, u) -> App(delta_sigma_reduce_weak t, u)
  | _ -> delta_sigma_reduce lt1 empty_mcontext
;;

exception UnificationError of lt*lt;;

let unify (menv:mcontext) (lenv:lcontext) (e1:lt) (e2:lt) : mcontext =
  match (e1, e2) with
  (*TYPE-SAME*)
  | (Type, Type) -> menv
  (*VAR-SAME*)
  (*RIGID-SAME*) (*we dont use E right now, we*)
  | (Var(x), Var(y)) ->
    if x <> y then raise (UnificationError(e1, e2));
    menv
  (*PROD-SAME*)
  | (Pi(x, t1, t2), Pi(y, t1, t2)) ->
    (*we \alpha-rename both*)
    (*TODO*)
      
  | _ -> raise (UnificationError(e1, e2))
;;

let test menv lenv e1 e2 = 
  try 
    let newctx = unify empty_mcontext [] e1 e2 in
    print_endline ("( "^(show_lt e1) ^ " ~ " ^ (show_lt e2) ^ " ) = " ^ show_mcontext newctx);
  with
  | UnificationError(e1, e2) ->
    print_endline ("Failed to unify " ^ show_lt e1 ^ " and " ^ show_lt e2);
  ;
;;

(*for tests*)
let unify_run () = 
  test empty_mcontext [] Type Type; 
  test empty_mcontext [] (Var("x")) (Var("y")); 
  test empty_mcontext [] (Var("x")) (Var("x")); 
;;
