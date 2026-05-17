open Expr
open Util

(*
The -reduce option of the executable
usage : -reduce <filename>
*)
let reduce_opt (content:string) : unit =
  let lt = parse_type content in
  let ctx = empty_env () in
  let current = ref lt in
  let stop = ref false in
  print_endline (affiche_lam !current);
  while not (!stop) do
    match betastep ctx !current with
    | Some next ->
      current := next;
      print_endline (affiche_lam !current)
    | None ->
      stop := true
  done
;;
