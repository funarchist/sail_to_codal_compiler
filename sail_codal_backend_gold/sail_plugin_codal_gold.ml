(****************************************************************************)
(* Minimal CODAL target plugin                                              *)
(* Wires the CODAL backend into Sail's Target system.                       *)
(****************************************************************************)

open Libsail

open Ast_util
open Interactive.State

(* No custom CLI flags for the minimal plugin *)
let codal_options : (Flag.t * Arg.spec * string) list = []

let codal_target out_file { ast; effect_info; env; default_sail_dir = _; _ } =
  (* Instantiate the code generator functor with sane defaults. *)
  let module Codalgen = Codal_backend.Codalgen (struct
    let generate_header = false
    let includes = []
    let header_includes = []
    let no_main = false
    let no_lib = false
    let no_rts = false
    let no_mangle = false
    let reserved_words = Util.StringSet.empty
    let overrides = Name_generator.Overrides.empty
    let branch_coverage = None
    let assert_to_exception = false
    let preserve_types = IdSet.empty
  end) in

  Reporting.opt_warnings := true;

  let echo_output, out_file = match out_file with Some f -> (false, f) | None -> (true, "out") in
  let basename = Filename.basename out_file in

  let header_opt, impl = Codalgen.compile_ast env effect_info basename ast in

  (* Write implementation file *)
  let impl_out = Util.open_output_with_check (out_file ^ ".c") in
  output_string impl_out.channel impl;
  flush impl_out.channel;
  Util.close_output_with_check impl_out;

  (* Optionally write header file *)
  (match header_opt with
  | Some header ->
      let header_out = Util.open_output_with_check (out_file ^ ".h") in
      output_string header_out.channel header;
      flush header_out.channel;
      Util.close_output_with_check header_out
  | None -> ());

  (* Echo implementation to stdout if no -o was supplied *)
  if echo_output then (
    output_string stdout impl;
    flush stdout
  )

let () =
  (* Register the target. We enable abstract types and runtime config so the
     frontend behaves like other codegen backends. *)
  ignore
    (Target.register
       ~name:"codal"
       ~options:codal_options
       ~supports_abstract_types:true
       ~supports_runtime_config:true
       codal_target)


