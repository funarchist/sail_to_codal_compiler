(****************************************************************************)
(* Minimal CODAL backend                                                    *)
(* Provides a tiny functor interface consumed by sail_plugin_codal_gold.    *)
(****************************************************************************)

open Libsail

open Type_check
open Effects
open Name_generator

module type CODALGEN_CONFIG = sig
  val generate_header : bool
  val includes : string list
  val header_includes : string list
  val no_main : bool
  val no_lib : bool
  val no_rts : bool
  val no_mangle : bool
  val reserved_words : Util.StringSet.t
  val overrides : string Name_generator.Overrides.t
  val branch_coverage : out_channel option
  val assert_to_exception : bool
  val preserve_types : IdSet.t
end

module Codalgen (Config : CODALGEN_CONFIG) = struct
  let compile_ast (_env : env) (_effects : side_effect_info) (basename : string) (_ast : typed_ast) : string option * string =
    (* Minimal output: a compilable C stub indicating the backend ran. *)
    let header =
      if Config.generate_header then
        Some (String.concat "\n"
                (["#pragma once";
                  "/* Minimal CODAL header */";
                  Printf.sprintf "/* module: %s */" basename] @
                 List.map (fun inc -> Printf.sprintf "#include \"%s\"" inc) Config.header_includes))
      else None
    in
    let body =
      String.concat "\n"
        ([ String.concat "\n" (List.map (fun inc -> Printf.sprintf "#include \"%s\"" inc) Config.includes);
           "/* Minimal CODAL implementation */";
           Printf.sprintf "/* module: %s */" basename;
           "int model_main(int argc, char **argv) { (void)argc; (void)argv; return 0; }" ])
      ^ "\n"
    in
    (header, body)
end


