(****************************************************************************)
(* Minimal CODAL target plugin                                              *)
(* Wires the CODAL backend into Sail's Target system.                       *)
(****************************************************************************)

open Libsail

open Interactive.State

(* No custom CLI flags for the minimal plugin *)
let codal_options : (Flag.t * Arg.spec * string) list = []

(* MINIMAL rewrites for CodAL backend - NO realize_mappings!
   
   We extract structural info (encdec mappings, execute function clauses)
   directly from the original AST. We do NOT use realize_mappings because
   it would convert mapping definitions into functions, destroying the
   bit pattern information we need for opcode generation.
   
   For semantic translation, we parse the execute function clauses directly
   from the AST and translate Sail expressions to CodAL. *)
let codal_rewrites =
  let open Rewrites in
  [
    ("instantiate_outcomes", [String_arg "codal"]);
    (* NO realize_mappings - we extract mappings from original AST! *)
    ("recheck_defs", []);
  ]

let codal_target out_file { ast; effect_info; env; default_sail_dir = _; _ } =
  (* Instantiate the code generator - simplified config, no JIB needed *)
  let module Codalgen = Codal_backend_gold.Codalgen (struct
    let generate_header = false
    let header_includes = []
  end) in

  Reporting.opt_warnings := true;

  let echo_output, out_file = match out_file with Some f -> (false, f) | None -> (true, "out") in
  let basename = Filename.basename out_file in

  (* Try to read the original SAIL source file *)
  let sail_source = 
    try
      let sail_file = basename ^ ".sail" in
      if Sys.file_exists sail_file then
        Util.read_whole_file sail_file
      else
        "/* Original SAIL source not found */"
    with
    | _ -> "/* Original SAIL source not available */"
  in

  let header_opt, impl = Codalgen.compile_ast env effect_info basename ast sail_source in

  (* Write main Codal output file *)
  let impl_out = Util.open_output_with_check (out_file ^ ".codal") in
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
       ~rewrites:codal_rewrites  (* Add the rewrites pipeline! *)
       ~supports_abstract_types:true
       ~supports_runtime_config:true
       codal_target)


