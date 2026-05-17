open Lib
open! Interactive
open Automatic
open Util
open Options

let nom_fichier = ref ""

let reduce = ref false
let alpha = ref false
let typecheck = ref false

let run () =
  Arg.parse
    [
      ("-reduce", Arg.Set reduce, "Reduce a lambda term");
      ("-alpha", Arg.Set alpha, "Checks in file containing \"u & v\", if u alpha equivalent to v");
      ("-typecheck", Arg.Set typecheck, "Checks in file containt \"t: tu\", if t has type tu")
    ] 
    (fun s -> nom_fichier := s)
    "";
  if !reduce then (
    match !nom_fichier with
    | "" -> failwith "Merci d'indiquer un fichier en argument."
    | filename -> 
      let content = In_channel.with_open_text filename In_channel.input_all in 
      reduce_opt content;
  )
  else
  if !alpha then 
    failwith "TODO : ALPHA" 
  else
  if !typecheck then 
    failwith "TODO : TYPECHECK" 
  else
  match !nom_fichier with
    | "" -> (
      (*Interactive UI*)
      interactive ();
    )
    | filename -> 
      (*We treat the given file linearly*)
      let content = In_channel.with_open_text filename In_channel.input_all in 
      automatic content;
  ;
;;

let _ = run ()
