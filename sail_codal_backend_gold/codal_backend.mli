open Libsail

open Jib
open Type_check
open Util
open Name_generator
open Codal_backend

val emit_codal : typed_ast -> string -> unit 

module type CODALGEN_CONFIG = sig
    (** If this is true, assadas will generate a separate header file, otherwise a single C file will be generated without
        a header file. *)
    val generate_header : bool
  
    (** A list of includes for the generated C file *)
    val includes : string list
  
    (** A list of includes for the generated header (if it is created). *)
    val header_includes : string list
  
    (** Do not generate a main function *)
    val no_main : bool
  
    (** Do not include sail.h automatically *)
    val no_lib : bool
  
    (** Do not include rts.h (the runtime), and do not generate code that requires any setup or teardown routines to be
        run by a runtime before executing any instruction semantics. *)
    val no_rts : bool
  
    (** Do not mangle generated C identifiers, prefer readable names when possible. *)
    val no_mangle : bool
  
    val reserved_words : Util.StringSet.t
  
    val overrides : string Name_generator.Overrides.t
  
    (** If [Some channel], the generated C code will be instrumented to track branch coverage information. Information
        about all the possible branches will be written to the provided output channel. *)
    val branch_coverage : out_channel option
  
    val assert_to_exception : bool
  
    val preserve_types : Ast_util.IdSet.t
  end
  
  module Codalgen (Config : CODALGEN_CONFIG) : sig
    val jib_of_ast : Env.t -> Effects.side_effect_info -> typed_ast -> cdef list * Jib_compile.ctx
    val compile_ast : Env.t -> Effects.side_effect_info -> string -> typed_ast -> string option * string
  end
  