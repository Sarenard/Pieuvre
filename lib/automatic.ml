open Util
open Tactic
open Expr

let check_theorem (gamma : context) (theorem : lambdaterm) (proof : tactic list)
(*TODO : make a better return type*)
  : bool (*if the proof is correct, for now*) =
  let goal = theorem in
  let term = ref (Goal(0, theorem)) in
  let tactics = ref proof in

  while !tactics <> [] do
    let myterm = numerote !term in
    let mygoals = get_goals myterm in
    match mygoals with
      | [] -> (
      failwith "Tactic when no goal remaining"
    )
    | goal :: _ -> (
      let tactic = List.hd !tactics in
      tactics := List.tl !tactics;
      let newterm = handle_tactic goal empty_env myterm tactic in
      term := newterm;
    );
  done;

  (*We finished*)
  (*We reduce the witness*)
  term := reduce !term;
  let debug = true in

  if debug then (
    print_endline "Witness of the proof :";
    affiche_lam !term; print_newline ();
    print_endline "Typechecking...";
  );

  try 
    typecheck gamma (!term) goal;
    if debug then (
      print_endline "Typechecking was a success !!";
    );
    true
  with Type_error -> (
    if debug then (
      print_endline "Typechecking failed...";
      print_endline (show_lambdaterm !term);
      print_endline (show_lambdaterm goal);
    );
    false
  )
;;

let automatic (content:string) : unit = 
  let elements = parse_statements content in
  print_endline (show_list show_statement elements);
  
  let rec handle_statements (gamma:context) (statements : statement list) =
    match statements with
    | Theorem(name, ty)::Proof(proof)::xs -> (
      let ok = check_theorem gamma ty proof in 
      if not ok then failwith ("Proof of theorem " ^ name ^ " is incorrect !");
      handle_statements ((name, ty)::gamma) xs;
    )
    
    | Inductive(_, _, _)::_ -> failwith "Inductive definitions are not supported yet"

    | Theorem(_, _)::_ -> failwith "Theorem without proof attached"
    | Proof(_)::_ -> failwith "Proof without theorem attached"
    | [] -> ()

  in handle_statements empty_env elements;
;;