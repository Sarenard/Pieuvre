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
    let mygoals = get_goals gamma myterm in
    match mygoals with
      | [] -> (
      failwith "Tactic when no goal remaining"
    )
    | goal :: _ -> (
      let tactic = List.hd !tactics in
      tactics := List.tl !tactics;
      let newterm = handle_tactic goal gamma myterm tactic in
      term := newterm;
    );
  done;

  (*We finished*)
  (*We reduce the witness*)
  term := reduce gamma !term;
  let debug = true in

  if debug then (
    print_endline "Witness of the proof :";
    print_endline (affiche_lam !term);
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
      print_endline (affiche_lam !term);
      print_endline (affiche_lam goal);
    );
    false
  )
;;

let automatic (content:string) : unit = 
  let elements = parse_statements content in
  print_endline (show_list show_statement elements);
  
  let rec handle_statements (gamma:context) (statements : statement list) =
    print_endline "Context :";
    print_endline (show_context gamma);
    print_newline ();
    match statements with
    | STheorem(name, ty)::SProof(proof)::xs -> (
      let ok = check_theorem gamma ty proof in 
      if not ok then failwith ("Proof of theorem " ^ name ^ " is incorrect !");
      (*We continue the execution*)
      let new_env = { gamma with gamma = (name, ty) :: gamma.gamma } in
      handle_statements new_env xs;
    )
    
    | SInductive(name, arity, constructors)::xs -> 
      (*
        TODO : We will later need to check if the inductive is small or big (when we will have universes)
        see https://link.springer.com/content/pdf/10.1007/BFb0037116.pdf page 10 (337)
        TODO : gérer les types du style option nat dans nat (ie les inductifs dans les inductifs dans la positivité)
        *)
      let new_env = ref gamma in
      (*we check that the inductive type is correct and add it to the env*)
      check_wellformed_inductive name (!new_env) arity constructors;
      let i = List.length (!new_env).inductive_types in
      new_env := {
        gamma = (name, arity) :: (!new_env).gamma;
        inductive_types = (!new_env).inductive_types @ [(name, arity, constructors)];
        values = (name, Inductive(i)) :: (!new_env).values;
      };
      (*we add constructors to the environment with the good type*)
      let handle_constructor j (name, ty) = (
        let new_var = (name, Constructor(i, j, [])) in
        new_env := { 
          gamma = (name, ty) :: (!new_env).gamma;
          inductive_types = (!new_env).inductive_types;
          values = new_var :: (!new_env).values; 
        };
      )
      in List.iteri handle_constructor constructors;
      (*we add the recursion principle to the environment with the good type*)
      let recursor = compute_recursor name arity constructors in
      new_env := { 
          gamma = (name ^ "_rec", recursor) :: (!new_env).gamma;
          inductive_types = (!new_env).inductive_types;
          values = (!new_env).values; 
      };
      (*We continue the execution*)
      handle_statements (!new_env) xs;

    | STheorem(_, _)::_ -> failwith "Theorem without proof attached"
    | SProof(_)::_ -> failwith "Proof without theorem attached"
    | [] -> ()

  in handle_statements empty_env elements;
;;
