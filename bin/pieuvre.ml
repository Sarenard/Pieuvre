open Lib
open! Interactive
open Automatic
open Options

let file_name = ref ""

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
    (fun s -> file_name := s)
    "";
  if !reduce then (
    match !file_name with
    | "" -> failwith "Please input a file."
    | filename -> 
      let content = In_channel.with_open_text filename In_channel.input_all in 
      reduce_opt content;
  )
  else
  if !alpha then (
    match !file_name with
    | "" -> failwith "Please input a file."
    | filename ->
      let content = In_channel.with_open_text filename In_channel.input_all in
      alpha_opt content
  )
  else
  if !typecheck then 
    match !file_name with
    | "" -> failwith "Please input a file."
    | filename ->
      let content = In_channel.with_open_text filename In_channel.input_all in
      typecheck_opt content
  else
  match !file_name with
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
