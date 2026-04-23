open Util
open Tactic
open Expr

let check_theorem (theorem : lambdaterm) (proof : tactic list)
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
      let newterm = handle_tactic goal myterm tactic in
      term := newterm;
    );
  done;

  (*We finished*)
  (*We reduce the witness*)
  term := reduce !term;
  (*We show a cool message*)
  print_endline "Witness of the proof :";
  affiche_lam !term; print_newline ();
  print_endline "Typechecking...";
  try 
  typecheck empty_env (!term) goal;
  print_endline "Typechecking was a success !!";
  true
  with Type_error -> (
    print_endline "Typechecking failed...";
    print_endline (show_lambdaterm !term);
    print_endline (show_lambdaterm goal);
    failwith "Typechecking failed...";
  )
;;

let automatic (content:string) : unit = 
  let elements = parse_statements content in
  print_endline (show_list show_statement elements);
  let rec handle_statements (statements : statement list) =
    match statements with
    | Theorem(_name, ty)::Proof(proof)::xs -> (
      let ok = check_theorem ty proof in ();
      handle_statements xs;
    )
    | Theorem(_, _)::[] -> failwith "Theorem without proof attached"
    | Proof(_)::[] -> failwith "Proof without theorem attached"
    | [] -> ()
  in handle_statements elements;
;;