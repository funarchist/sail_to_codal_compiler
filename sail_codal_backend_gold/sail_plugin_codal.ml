(* Minimal plugin registration for Codal backend *)
open Libsail

open Ast_util
open Interactive.State

(*I give no options so no need to define 
-opt_ vars, 
-codal_options
-codal_rewrites, 
-collect_codal_name_info
-no header part
-No reference to any of this in target deceleration
-NO building option
-No if not output file name put into echo
-No check for reserve or overrides names

*)  
let opt_assert_to_exception = ref false
let opt_branch_coverage = ref None
let opt_build = ref false
let opt_generate_header = ref false
let opt_includes_c : string list ref = ref []
let opt_includes_h : string list ref = ref []
let opt_no_lib = ref false
let opt_no_main = ref false
let opt_no_mangle = ref false
let opt_no_rts = ref false
let opt_preserve_types = ref IdSet.empty
let opt_specialize_c = ref false



let codal_options =
  [


  
  ]

let codal_target out_file { ast; effect_info; env; default_sail_dir; _ }=
  (* ast: the Sail AST to be compiled., where it comes from?
  effect_info: information about side effects in the Sail program.,env: ?,default_sail_dir: default Sail directory.
  *)
  (*
  let reserveds, overrides = collect_c_name_info ast in
  *)
  let module Codalgen = Codal_backend.Codalgen (struct
    let generate_header = !opt_generate_header
    let includes = !opt_includes_c
    let header_includes = !opt_includes_h
    let no_main = !opt_no_main
    let no_lib = !opt_no_lib
    let no_rts = !opt_no_rts
    let no_mangle = !opt_no_mangle
    let reserved_words = "reserveds"
    let overrides = "overrides"
    let branch_coverage = !opt_branch_coverage
    let assert_to_exception = !opt_assert_to_exception
    let preserve_types = !opt_preserve_types
    end) in
    Reporting.opt_warnings := true;
    (*Turns on compiler warnings*)
    let echo_output, out_file = match out_file with Some f -> (false, f) | None -> (true, "out") in
    (*Checks whether in CLI output file name provided if not gives name out, if yes takes provided name no cli message*)
    let basename = Filename.basename out_file in
    (*std Filename folder which is used in compile_ast*)

    let header_opt, impl = Codalgen.compile_ast env effect_info basename ast in


    (* In here output of the compile ast is C code as generated string it is put into
    impl(implementation) and we can create header optionally but not in this case *)
    (*Is ast->anf->jib transform happening in compile_Ast?*)
    let impl_out = Util.open_output_with_check (out_file ^ ".c") in
    (*We create name  of the file that string will be printed in*)
    output_string impl_out.channel impl;
    (*stdlib/Outchannel.output_string Write the string on the given output channel.*)
    flush impl_out.channel;
    (*Outchannel.flush flushes the output channel. *)
    (*Is generated codal code can be built?*)
    (*
    -Util.close_output_with_check
    -match header_opt with
    -if echo_output then (
    -if  !opt_build then (
    -if 
    *)


    (* If header is generated, write it *)
    (match header_opt with
    | Some header ->
        let header_out = Util.open_output_with_check (out_file ^ ".h") in
        output_string header_out.channel header;
        flush header_out.channel
    | None -> ());

    (* Echo output if requested *)
    if echo_output then
      Printf.printf "Codal code written to %s.codal\n" out_file



  
let () =
    (*
    -Pragmas
    -Some target options
    *)
  Target.register ~name:"codal" codal_target

