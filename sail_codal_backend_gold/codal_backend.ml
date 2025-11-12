open Libsail

open Ast
open Ast_util
open Jib
open Jib_compile
open Jib_util
open Jib_visitor
open Type_check
open PPrint
open Value2
open Util
open Name_generator 
module Document = Pretty_print_sail.Document

open Anf

(* following until Converting sail types to C types
All can be defined no problem, it doesnt have to be used anyway.
big change  asdasdasdasd
*)

module Big_int = Nat_big_num

let opt_static = ref false
let static () = if !opt_static then "static " else ""
let opt_prefix = ref "z"
let opt_extra_params = ref None
let opt_extra_arguments = ref None

let extra_params () = match !opt_extra_params with Some str -> str ^ ", " | _ -> ""

let extra_arguments is_extern = match !opt_extra_arguments with Some str when not is_extern -> str ^ ", " | _ -> ""

(* Optimization flags *)
let optimize_primops = ref false
let optimize_hoist_allocations = ref false
let optimize_alias = ref false
let optimize_fixed_int = ref false
let optimize_fixed_bits = ref false

let ngensym = symbol_generator ()

let c_error ?loc:(l = Parse_ast.Unknown) message = raise (Reporting.err_general l ("\nC backend: " ^ message))

(**************************************************************************)
(* NO 2. Converting sail types to C types          LLIne:86                           *)
(**************************************************************************)
(*This part whole dont change sail to jib types, no need to change anything here*)
let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

(** This function is used to split types into those we allocate on the stack, versus those which need to live on the
    heap, or otherwise require some additional memory management.

    This is roughly the same distinction that Rust makes between copy and non-copy types. *)
let rec is_stack_ctyp ctx ctyp =
  match ctyp with
  | CT_fbits _ | CT_sbits _ | CT_bit | CT_unit | CT_bool | CT_enum _ -> true
  | CT_fint n -> n <= 64
  | CT_lint when !optimize_fixed_int -> true
  | CT_lint -> false
  | CT_lbits when !optimize_fixed_bits -> true
  | CT_lbits -> false
  | CT_real | CT_string | CT_list _ | CT_vector _ | CT_fvector _ -> false
  | CT_struct (_, _) ->
      let _, fields = struct_field_bindings Parse_ast.Unknown ctx ctyp in
      Bindings.for_all (fun _ ctyp -> is_stack_ctyp ctx ctyp) fields
  | CT_variant (_, _) -> false
  | CT_tup ctyps -> List.for_all (is_stack_ctyp ctx) ctyps
  | CT_ref _ -> true
  | CT_poly _ -> true
  | CT_float _ -> true
  | CT_rounding_mode -> true
  (* Is a reference to some immutable JSON data *)
  | CT_json -> true
  | CT_json_key -> true
  | CT_constant n -> Big_int.less_equal (min_int 64) n && Big_int.greater_equal n (max_int 64)
  | CT_memory_writes -> false

let v_mask_lower i = V_lit (VL_bits (Util.list_init i (fun _ -> Sail2_values.B1)), CT_fbits i)

let hex_char =
  let open Sail2_values in
  function
  | '0' -> [B0; B0; B0; B0]
  | '1' -> [B0; B0; B0; B1]
  | '2' -> [B0; B0; B1; B0]
  | '3' -> [B0; B0; B1; B1]
  | '4' -> [B0; B1; B0; B0]
  | '5' -> [B0; B1; B0; B1]
  | '6' -> [B0; B1; B1; B0]
  | '7' -> [B0; B1; B1; B1]
  | '8' -> [B1; B0; B0; B0]
  | '9' -> [B1; B0; B0; B1]
  | 'A' | 'a' -> [B1; B0; B1; B0]
  | 'B' | 'b' -> [B1; B0; B1; B1]
  | 'C' | 'c' -> [B1; B1; B0; B0]
  | 'D' | 'd' -> [B1; B1; B0; B1]
  | 'E' | 'e' -> [B1; B1; B1; B0]
  | 'F' | 'f' -> [B1; B1; B1; B1]
  | _ -> failwith "Invalid hex character"

let literal_to_fragment (L_aux (l_aux, _)) =
  match l_aux with
  | L_num n when Big_int.less_equal (min_int 64) n && Big_int.less_equal n (max_int 64) ->
      Some (V_lit (VL_int n, CT_fint 64))
  | L_hex str when String.length str <= 16 ->
      let padding = 16 - String.length str in
      let padding = Util.list_init padding (fun _ -> Sail2_values.B0) in
      let content = Util.string_to_list str |> List.map hex_char |> List.concat in
      Some (V_lit (VL_bits (padding @ content), CT_fbits (String.length str * 4)))
  | L_unit -> Some (V_lit (VL_unit, CT_unit))
  | L_true -> Some (V_lit (VL_bool true, CT_bool))
  | L_false -> Some (V_lit (VL_bool false, CT_bool))
  | _ -> None

let sail_create ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sCREATE(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_recreate ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sRECREATE(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_copy ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sCOPY(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_kill ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sKILL(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_equal ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sEQUAL(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_convert_of ?(prefix = "") ?(suffix = "") ctyp1 ctyp2 fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sCONVERT_OF(%s, %s)(%s)%s" prefix ctyp1 ctyp2 s suffix) fmt

let c_function ~return decl body =
  string return ^^ space ^^ decl ^^ space ^^ nest 2 (lbrace ^^ hardline ^^ separate hardline body) ^^ hardline ^^ rbrace

let c_stmt s = string s ^^ semi

let c_assign x op y = separate space [x; string op; y] ^^ semi

let c_for iter body =
  string "for" ^^ space ^^ iter ^^ space ^^ nest 2 (lbrace ^^ hardline ^^ separate hardline body) ^^ hardline ^^ rbrace

let c_cond_block c block = if c then block else []

let c_if_block b = nest 2 (lbrace ^^ hardline ^^ separate hardline b) ^^ hardline ^^ rbrace

let c_if cond then_block = string "if" ^^ space ^^ cond ^^ space ^^ c_if_block then_block

let c_if_else cond then_block else_block =
  string "if" ^^ space ^^ cond ^^ space ^^ c_if_block then_block ^^ space ^^ string "else" ^^ space
  ^^ c_if_block else_block

let c_return exp = string "return" ^^ space ^^ exp ^^ semi

(*This convert sail to jib types, no need to change anything here*)
module C_config (Opts : sig 
(*
-branch_coverage
-assert_to_exception
-preserve_types
*)
end) : CONFIG = struct
    (*Its main job is to define how Sail types map to jib types in the JIB compiler backend.*)
    let rec convert_typ ctx typ =
      let (Typ_aux (typ_aux, l) as typ) = Env.expand_synonyms ctx.local_env typ in
      match typ_aux with
      | Typ_id id when string_of_id id = "bit" -> CT_bit
      | Typ_id id when string_of_id id = "bool" -> CT_bool
      | Typ_id id when string_of_id id = "int" -> CT_lint
      | Typ_id id when string_of_id id = "nat" -> CT_lint
      | Typ_id id when string_of_id id = "unit" -> CT_unit
      | Typ_id id when string_of_id id = "string" -> CT_string
      | Typ_id id when string_of_id id = "string_literal" -> CT_string
      | Typ_id id when string_of_id id = "real" -> CT_real
      | Typ_app (id, _) when string_of_id id = "atom_bool" -> CT_bool
      | Typ_app (id, args) when string_of_id id = "itself" -> convert_typ ctx (Typ_aux (Typ_app (mk_id "atom", args), l))
      | Typ_app (id, _) when string_of_id id = "range" || string_of_id id = "atom" || string_of_id id = "implicit" ->
        begin
          match destruct_range Env.empty typ with
          | None -> assert false (* Checked if range type in guard *)
          | Some (kids, constr, n, m) -> (
              let ctx =
                {
                  ctx with
                  local_env = add_existential Parse_ast.Unknown (List.map (mk_kopt K_int) kids) constr ctx.local_env;
                }
              in
              match (nexp_simp n, nexp_simp m) with
              | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
                when Big_int.less_equal (min_int 64) n && Big_int.less_equal m (max_int 64) ->
                  CT_fint 64
              | n, m ->
                  if
                    prove __POS__ ctx.local_env (nc_lteq (nconstant (min_int 64)) n)
                    && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_int 64)))
                  then CT_fint 64
                  else CT_lint
            )
        end
      | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" -> CT_list (ctyp_suprema (convert_typ ctx typ))
      (* When converting a sail bitvector type into C, we have three options in order of efficiency:
         - If the length is obviously static and smaller than 64, use the fixed bits type (aka uint64_t), fbits.
         - If the length is less than 64, then use a small bits type, sbits.
         - If the length may be larger than 64, use a large bits type lbits. *)
      | Typ_app (id, [A_aux (A_nexp n, _)]) when string_of_id id = "bitvector" -> begin
          match nexp_simp n with
          | Nexp_aux (Nexp_constant n, _) when Big_int.less_equal n (Big_int.of_int 64) -> CT_fbits (Big_int.to_int n)
          | n when prove __POS__ ctx.local_env (nc_lteq n (nint 64)) -> CT_sbits 64
          | _ -> CT_lbits
        end
      | Typ_app (id, [A_aux (A_nexp _, _); A_aux (A_typ typ, _)]) when string_of_id id = "vector" ->
          CT_vector (convert_typ ctx typ)
      | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "register" -> CT_ref (convert_typ ctx typ)
      | Typ_id id when Bindings.mem id ctx.records -> CT_struct (id, [])
      | Typ_app (id, typ_args) when Bindings.mem id ctx.records ->
          let ctyp_args =
            List.filter_map
              (function A_aux (A_typ typ, _) -> Some (ctyp_suprema (convert_typ ctx typ)) | _ -> None)
              typ_args
          in
          CT_struct (id, ctyp_args)
      | Typ_id id when Bindings.mem id ctx.variants -> CT_variant (id, []) |> transparent_newtype ctx
      | Typ_app (id, typ_args) when Bindings.mem id ctx.variants ->
          let ctyp_args =
            List.filter_map
              (function A_aux (A_typ typ, _) -> Some (ctyp_suprema (convert_typ ctx typ)) | _ -> None)
              typ_args
          in
          CT_variant (id, ctyp_args) |> transparent_newtype ctx
      | Typ_id id when Bindings.mem id ctx.enums -> CT_enum id
      | Typ_tuple typs -> CT_tup (List.map (convert_typ ctx) typs)
      | Typ_exist _ -> begin
          (* Use Type_check.destruct_exist when optimising with SMT, to
             ensure that we don't cause any type variable clashes in
             local_env, and that we can optimize the existential based
             upon its constraints. *)
          match destruct_exist typ with
          | Some (kids, nc, typ) ->
              let env = add_existential l kids nc ctx.local_env in
              convert_typ { ctx with local_env = env } typ
          | None -> raise (Reporting.err_unreachable l __POS__ "Existential cannot be destructured!")
        end
      | Typ_var kid -> CT_poly kid
      | _ -> c_error ~loc:l ("No C type for type " ^ string_of_typ typ)
  
(**************************************************************************)
(* NO 3. Optimization of primitives and literals   line.294                          *)
(**************************************************************************)
(*
-c_literals
-is_bitvector
-value_of_aval_bit
-never_optimize
-c_aval
-analyze_functions
-analyze_primop
-analyze_primop
-optimize_anf

 let unroll_loops = None
  let make_call_precise _ _ _ _ = true
  let ignore_64 = false
  let struct_value = false
  let tuple_value = false
  let use_real = false
  let branch_coverage = Opts.branch_coverage
  let track_throw = true
  let assert_to_exception = Opts.assert_to_exception
  let use_void = false
  let eager_control_flow = false
  let preserve_types = Opts.preserve_types
  let fun_to_wires = Bindings.empty

-fix_early_heap_return
-fix_early_stack_return
-insert_heap_returns
-add_local_labels'
-add_local_labels

*)



(**************************************************************************)
(* NO 5. Optimizations       lINE:634                                               *)
(**************************************************************************)

(**************************************************************************)
(* 6. Code generation     LINE:920                                                *)
(**************************************************************************)

(* 
-mk_regexp_check
-valid_c_identifier
-c_int_type_name  
-type file_doc
-to_impl
*)
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

end

module Codalgen (Config : CODALGEN_CONFIG) = struct (*959-2582*)
  open Printf
 (*This section of the code is critical in the code generation pipeline because it controls how identifiers (variables, functions, exceptions, etc.) from Sail’s intermediate representation are transformed into valid, collision-free C code names.*)
  let has_prefix prefix s =
    if String.length s < String.length prefix then false else String.sub s 0 (String.length prefix) = prefix

  let has_sail_prefix s = has_prefix "sail_" s || has_prefix "Sail_" s || has_prefix "SAIL_" s
  module NameGen =
    Name_generator.Make
    (struct
      type style = unit
      (*
      let allowed s =
        let valid_name s =
          valid_c_identifier s
          && (not (Util.StringSet.mem s Keywords.c_reserved_words))
          && (not (Util.StringSet.mem s Keywords.c_used_words))
          && (not (Util.StringSet.mem s Config.reserved_words))
          && (not (has_sail_prefix s))
          && not (c_int_type_name s)
        in
        (not Config.no_mangle) || valid_name s
      *)
      let pretty () s = if Config.no_mangle then s else Util.zencode_string s

      let mangle () s = Util.zencode_string s

      let variant s = function 0 -> s | n -> s ^ string_of_int n

  (*    let overrides = Config.overrides *)
    end)
    ()

    (*Converts an identifier id into its string representation using*)
    let sgen_id id = NameGen.to_string () id
    (* Generates a unique string identifier from a pair of an id and a list of types ctyps.*)
    let sgen_uid (id, ctyps) =
      match ctyps with
      | [] -> NameGen.to_string () id
      | _ -> NameGen.translate () (string_of_id id ^ "#" ^ Util.string_of_list "_" string_of_ctyp ctyps)
    (* Defines a function to produce a string name for various symbol kinds (variables, exceptions, memory, etc.) with optional SSA numbering.*)
    let sgen_name =
      let ssa_num n = if n = -1 then "" else "/" ^ string_of_int n in
      function
      | Gen (v1, v2, n) -> NameGen.to_string () (mk_id (sprintf "%d.%d" v1 v2)) ^ ssa_num n
      | Name (id, n) -> NameGen.to_string () id ^ ssa_num n
      | Have_exception n -> "have_exception" ^ ssa_num n
      | Return n -> "return" ^ ssa_num n
      | Current_exception n -> "(*current_exception)" ^ ssa_num n
      | Throw_location n -> "throw_location" ^ ssa_num n
      | Memory_writes n -> "memory_writes" ^ ssa_num n
      | Channel (chan, n) -> (
          match chan with Chan_stdout -> "stdout" ^ ssa_num n | Chan_stderr -> "stderr" ^ ssa_num n
        )
   (*Wraps the generated string from sgen_id into a string value for code generation.*)
    let codegen_id id = string (sgen_id id)
  (*Generates a function identifier string, optionally prefixing/mangling it depending on configuration.*)
    let sgen_function_id id =
      let str = NameGen.to_string () id in
      if Config.no_mangle then str else !opt_prefix ^ String.sub str 1 (String.length str - 1)
  (* Same as sgen_function_id but for unique function identifiers (includes type parameters in the name).*)
    let sgen_function_uid uid =
      let str = sgen_uid uid in
      if Config.no_mangle then str else !opt_prefix ^ String.sub str 1 (String.length str - 1)
  (*Converts the mangled or unmangled function identifier into a string form for code generation.*)
    let codegen_function_id id = string (sgen_function_id id)

  (* Convert Jib Types to Codal Types *)
  (*There exists 25 types in Jib*)
  let rec sgen_ctyp = function (*depends sgen_id,sgen_ctyp*)
 (* | CT_unit ->     CT_unit represents the Sail unit type (like void in C, () in OCaml).
  | CT_bit ->     A single bit value.  *) 
  | CT_bool -> "bool"
  (*Fixed Variable Interger Types*)
 (* | CT_fbits _ ->   Fixed-width unsigned bitvector.In the C backend, these are lowered to uint64_t for performance (up to 64 bits).
  | CT_sbits _ ->     Fixed-width signed bitvector.
  | CT_fint _ ->      Fixed-width integer type (signed).
  | CT_constant _ ->      A literal constant integer value.
  | CT_lint ->             Large (arbitrary precision) integer type.
  (*Large & Complex Bitvector Types*)
  | CT_lbits ->              (*Large (arbitrary precision) bitvector."lbits" is a runtime struct for dynamically sized bitvectors.*)
  (Compound Types (Tuples, Structs, Variants, Enums))
  | CT_tup _ as tup ->      (*A tuple type in Sail.*)
  | CT_struct (id, _) ->       Struct type
  | CT_enum id ->              Enum type
  | CT_variant (id, _) ->      mapped to tagged struct type in C
  (List, Vector, and Array Types)
  | CT_list _ as l ->          List type
  | CT_vector _ as v -> 
  | CT_fvector (_, typ) -> 
  (Strings & Special Data Types)
  | CT_string ->
  | CT_real ->
  | CT_json -> 
  | CT_json_key -> 
  (References, Floating Point, Rounding)
  | CT_ref ctyp ->    (*Generates a pointer type in C.*)
  | CT_float n ->      (Floating-point with precision n.)
  | CT_rounding_mode ->  (Rounding mode for floating-point.Stored as a small integer type.) 
  (Memory, Polymorphism)
  | CT_memory_writes ->
  | CT_poly _ -> *)   (* (Polymorphic type. "POLY" indicates that monomorphization wasn’t done (likely an error in codegen if reached).)*)
  (*We have sgen_ctype_name,Used in generated function names, helper macros, and type-based dispatch where the type is part of a name (no *, no C keywords).*)
  (*-sgen_const_ctype dep sgen_ctype**)
  (*-sgen_mask*)

  let sgen_value = function (*dep sgen_id*)
 (* | VL_bits [] -> 
  | VL_bits bs -> 
  | VL_int i -> *)
  | VL_bool true -> "true"
  | VL_bool false -> "false"
(*  | VL_unit -> 
  | VL_bit Sail2_values.B0 -> 
  | VL_bit Sail2_values.B1 -> 
  | VL_bit Sail2_values.BU -> 
  | VL_real str -> 
  | VL_string str -> 
  | VL_enum element -> 
  | VL_ref r -> 
  | VL_undefined -> *)

  (*-sgen_tuple_id dep sgen_id*)
  (*sgen_cval are value constructors dep sgen_name,sgen_id,sgen_value,sgen_call,sgen_cval,sgen_tuple_id,sgen_uid*)
  let rec sgen_cval = function
  | V_id (id, _) ->  sgen_name id (*Most common for variables*)
  (*| V_member (id, _) ->  *)
  | V_lit (vl, _) -> sgen_value vl  (*Most common for literaral**)
  | V_call (op, cvals) -> sgen_call op cvals
  (*| V_field (f, field, _) -> 
  | V_tuple_member (f, _, n) -> 
  | V_ctor_kind (f, ctor) -> 
  | V_struct (fields, _) ->
  | V_ctor_unwrap (f, ctor, _) -> 
  | V_tuple _ -> 
  *)
  (*These are operator arithmetic, logical, it prints in C format in c bakcned**)
  and sgen_call op cvals = (*sgen_cval, cval_ctyp*)
      match (op, cvals) with
   (*      | Bnot, [v] -> 
      | Band, vs ->
      | Bor, vs -> 
      | List_hd, [v] -> 
      | List_tl, [v] ->
      | List_is_empty, [v] -> 
      | Eq, [v1; v2] -> begin
      | Neq, [v1; v2] -> begin *)
      | Ilt, [v1; v2] -> sprintf "(%s < %s)" (sgen_cval v1) (sgen_cval v2)
  (*    | Igt, [v1; v2] -> 
      | Ilteq, [v1; v2] -> 
      | Igteq, [v1; v2] ->  *)
      | Iadd, [v1; v2] -> sprintf "(%s + %s)" (sgen_cval v1) (sgen_cval v2)
  (*  | Isub, [v1; v2] -> 
      | Unsigned 64, [vec] -> 
      | Signed 64, [vec] ->
      | Bvand, [v1; v2] -> begin
      | Bvnot, [v] -> begin
      | Bvor, [v1; v2] -> begin
      | Bvxor, [v1; v2] -> begin
      | Bvadd, [v1; v2] -> begin
      | Bvsub, [v1; v2] -> begin
      | Bvaccess, [vec; n] -> begin
      | Slice len, [vec; start] -> begin
      | Sslice 64, [vec; start; len] -> begin
      | Set_slice, [vec; start; slice] -> begin
      | Zero_extend n, [v] -> begin
      | Sign_extend n, [v] -> begin
      | Replicate n, [v] -> begin
      | Concat, [v1; v2] -> begin
      | Get_abstract, [v] -> 
      | Ite, [i; t; e] -> 
      | String_eq, [s1; s2] -> 
      | _, _ -> 
   *)   

  (*generating the parameter string for function calls, depending on the compile-time type of the value *)
 (*      let sgen_cval_param cval = (*depends sgen_cval*)
          | CT_lbits -> 
          | CT_sbits _ -> 
          | CT_fbits len -> 
          | _ ->
  (* C backend l-expression (l-value) generator — it translates jib clexp patterns into the C code that points to or dereferences the right variable or struct field.*)
        let rec sgen_clexp l = function (*sgen_name,sgen_clexp,sgen_id,sgen_tuple_id*)
          | CL_id (Have_exception _, _) -> 
          | CL_id (Current_exception _, _) ->
          | CL_id (Throw_location _, _) ->
          | CL_id (Memory_writes _, _) -> 
          | CL_id (Channel _, _) -> 
          | CL_id (Return _, _) -> 
          | CL_id (name, _) -> 
          | CL_field (clexp, field, _) -> 
          | CL_tuple (clexp, n) -> 
          | CL_addr clexp ->
          | CL_void _ -> 
          | CL_rmw _ ->
  (*It generates the C expression corresponding to a left expression (clexp), but as a value, not as a pointer.*)
        let rec sgen_clexp_pure l = function
          | CL_id (Have_exception _, _) -> 
          | CL_id (Current_exception _, _) -> 
          | CL_id (Throw_location _, _) -> 
          | CL_id (Memory_writes _, _) -> 
          | CL_id (Channel _, _) -> 
          | CL_id (Return _, _) -> 
          | CL_id (name, _) -> 
          | CL_field (clexp, field, _) -> 
          | CL_tuple (clexp, n) -> 
          | CL_addr clexp -> 
          | CL_void _ -> 
          | CL_rmw _ -> 
        (** Generate instructions to copy from a cval to a clexp. This will insert any needed type conversions from big
            integers to small integers (or vice versa), or from arbitrary-length bitvectors to and from uint64 bitvectors as
            needed. *)

      (*Generates C code to copy a value (cval) into a location (clexp).

  Handles type conversions if the source and target types differ (e.g., big integer ↔ small integer, variable-length vector ↔ fixed 64-bit vector, tuple types, etc.).*)
        let rec codegen_conversion l ctx clexp cval = (*depends is_stack_ctyp,sgen_clexp_,sgen_clexp_pure,clexp,sgen_cval*)
          (* When both types are equal, we don't need any conversion. *)
          | _, _ when ctyp_equal ctyp_to ctyp_from -> (*dep sgne_ctype_name*)
          | CT_ref _, _ -> c
          | ( (CT_vector ctyp_elem_to | CT_fvector (_, ctyp_elem_to)),
              (CT_vector ctyp_elem_from | CT_fvector (_, ctyp_elem_from)) ) -> (*dep ngensym,sail_kill*)
          (*vector to vector conversion up*)
          (* If we have to convert between tuple types, convert the fields individually. *)
          | CT_tup ctyps_to, CT_tup ctyps_from when List.length ctyps_to = List.length ctyps_from ->
          (* For anything not special cased, just try to call a appropriate CONVERT_OF function. *)
          | _, _ when is_stack_ctyp ctx (clexp_ctyp clexp) ->
              (*sail_convert_of*)
          | _, _ ->
  (*codegen_conversion;Correct type-safe assignment in generated C code.,Calls appropriate create/copy/kill helpers for heap-managed types.
  Recursively handles nested structures (vectors, tuples).*)
      
    (*-squash_empty
    -sq_separate_map*)
  (*codegen_instr takes an intermediate instruction (from the compiler’s internal IR) and converts it into C code as a formatted string.
  fid = function ID (used for context-specific codegen)
  ctx = codegen context (tracks externs, stack types, etc.)
  I_aux (instr, (_, l)) = the instruction plus location l for error reporting
  *)

*) 
  let rec codegen_instr fid ctx (I_aux (instr, (_, l))) =
      match instr with
      | I_decl (ctyp, id) when is_stack_ctyp ctx ctyp -> ksprintf string "  %s %s;" (sgen_ctyp ctyp) (sgen_name id)
      | I_decl (ctyp, id) ->
      | I_copy (clexp, cval) -> codegen_conversion l ctx clexp cval
      | I_jump (cval, label) -> ksprintf string "  if (%s) goto %s;" (sgen_cval cval) label
      | I_if (cval, [], else_instrs) -> codegen_instr fid ctx (iif l (V_call (Bnot, [cval])) else_instrs [])
      | I_if (cval, [then_instr], []) ->
      | I_if (cval, then_instrs, []) ->
      | I_if (cval, then_instrs, else_instrs) ->
      | I_block instrs ->
      | I_try_block instrs ->
      | I_funcall (x, special_extern, f, args) ->
      | I_clear (ctyp, _) when is_stack_ctyp ctx ctyp -> empty
      | I_clear (ctyp, id) -> sail_kill ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
      | I_init (ctyp, id, init) -> 
      | I_reinit (ctyp, id, cval) ->
      | I_reset (ctyp, id) when is_stack_ctyp ctx ctyp ->
      | I_reset (ctyp, id) -> sail_recreate ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
      | I_return cval -> twice space ^^ c_return (string (sgen_cval cval))
      | I_throw _ -> c_error ~loc:l "I_throw reached code generator"
      | I_undefined ctyp ->
      | I_comment str -> string ("  /* " ^ str ^ " */")
      | I_label str -> string (str ^ ": ;")
      | I_goto str -> string (Printf.sprintf "  goto %s;" str)
      | I_raw _ when ctx.no_raw -> empty
      | I_raw str -> string ("  " ^ str)
      | I_end _ -> assert false
      | I_exit _ -> string ("  sail_match_failure(\"" ^ String.escaped (string_of_id fid) ^ "\");")

      let codegen_type_def ctx =
        let open Printf in
        function
        | CTD_abstract (id, ctyp, inst) -> (*Generates C code for abstract Sail types.*)
        | CTD_enum (id, (first_id :: _ as ids)) -> (*Generates C code for abstract Sail types.*)
        | CTD_enum (id, []) -> c_error ("Cannot compile empty enum " ^ string_of_id id)
        | CTD_abbrev (id, ctyp) -> (*Creates a typedef in C for a type abbreviation.*)
        | CTD_struct (id, _, ctors) -> (*Generates a C struct with:*)
        | CTD_variant (id, _, tus) -> (*Generates tagged unions (sum types).*)
 
        (** GLOBAL: because C doesn't have real anonymous tuple types (anonymous structs don't quite work the way we need)
          every tuple type in the spec becomes some generated named struct in C. This is done in such a way that every
          possible tuple type has a unique name associated with it. This global variable keeps track of these generated
          struct names, so we never generate two copies of the struct that is used to represent them in C. The way this
          works is that codegen_def scans each definition's type annotations for tuple types and generates the required
          structs using codegen_type_def before the actual definition is generated by codegen_def'. This variable should be
          reset to empty only when the entire AST has been translated to C. **)
 
      let generated = ref IdSet.empty
    
      (*It generates and registers a unique struct type for a tuple’s component types if it hasn’t been created before.*)
      let codegen_tup ctx ctyps =
        (*It generates C code for a linked list type of a given element type, 
        including the struct definition, reference counting, initialization, cleanup, copying,
        construction (cons), element access, equality, and an undefined placeholder function.        *)

  let codegen_list ctx ctyp =
      let codegen_node =
      let codegen_list_init =
      let codegen_list_clear =
      let codegen_list_recreate =
      let codegen_inc_reference_count =
      let codegen_dec_reference_count =
      let codegen_list_copy =
      let codegen_cons =
      let codegen_pick =
      let codegen_list_equal =
      let codegen_list_undefined =


    (*This function generates C code for vector operations 
    (create, initialize, update, access, compare, clear, etc.) for a given Sail type if it hasn’t been generated already.*)    
    (* Generate functions for working with non-bit vectors of some specific type. *)
  let codegen_vector ctx ctyp =
      let vector_typedef =
      let vector_decl =
      let vector_init =
      let vector_set =
      let vector_clear =
      let vector_reinit =
      let vector_update =
      let internal_vector_update =
      let vector_access =
      let internal_vector_init =
      let vector_undefined =
      let vector_equal =
      let vector_length =

  (*is_decl checks if an instruction is a declaration.*)
  let is_decl = function I_aux (I_decl _, _) -> true | _ -> false
  (*codegen_decl generates a C declaration statement for a given Sail type and identifier.*)
  let codegen_decl = function
    | I_aux (I_decl (ctyp, id), _) -> string (Printf.sprintf "%s %s;" (sgen_ctyp ctyp) (sgen_name id))
    | _ -> assert false
  (*codegen_alloc generates memory allocation code for a declared variable unless it is a stack type.*)
  let codegen_alloc ctx = function
    | I_aux (I_decl (ctyp, _), _) when is_stack_ctyp ctx ctyp -> empty
    | I_aux (I_decl (ctyp, id), _) -> sail_create ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | _ -> assert false

  (*codegen_def' generates C code for each type of Sail definition 
  (registers, functions, types, startup/finish code, let-bindings, and pragmas) based on the context.*)

    let codegen_def' ctx (CDEF_aux (aux, _)) = (*depends on*)
      match aux with
      | CDEF_register (id, ctyp, _) ->
      | CDEF_val (id, _, arg_ctyps, ret_ctyp, _) ->
      | CDEF_fundef (id, ret_arg, args, instrs) ->
      | CDEF_type ctype_def -> codegen_type_def ctx ctype_def
      | CDEF_startup (id, instrs) ->
      | CDEF_finish (id, instrs) ->
      | CDEF_let (number, bindings, instrs) ->
      | CDEF_pragma _ -> []
  
    (** As we generate C we need to generate specialized version of tuple, list, and vector type. These must be generated
        in the correct order. The ctyp_dependencies function generates a list of c_gen_typs in the order they must be
        generated. Types may be repeated in ctyp_dependencies so it's up to the code-generator not to repeat definitions
        pointlessly (using the !generated variable) *)
    (*c_gen_typ represents specialized C types that need to be generated, such as tuples, lists, or vectors.*)
        type c_gen_typ = CTG_tup of ctyp list | CTG_list of ctyp | CTG_vector of ctyp
  
     (*ctyp_dependencies computes the order of dependent specialized C types needed for code generation.*)   
    let rec ctyp_dependencies = function
      | CT_tup ctyps -> List.concat (List.map ctyp_dependencies ctyps) @ [CTG_tup ctyps]
      | CT_list ctyp -> ctyp_dependencies ctyp @ [CTG_list ctyp]
      | CT_vector ctyp | CT_fvector (_, ctyp) -> ctyp_dependencies ctyp @ [CTG_vector ctyp]
      | CT_ref ctyp -> ctyp_dependencies ctyp
      | CT_struct (_, ctyps) | CT_variant (_, ctyps) -> List.concat (List.map ctyp_dependencies ctyps)
      | CT_lint | CT_fint _ | CT_lbits | CT_fbits _ | CT_sbits _ | CT_unit | CT_bool | CT_real | CT_bit | CT_string
      | CT_enum _ | CT_poly _ | CT_constant _ | CT_float _ | CT_rounding_mode | CT_memory_writes | CT_json | CT_json_key
        ->
          []
  
     (*codegen_ctg generates C code for a specialized tuple, list, or vector type.*)     
    let codegen_ctg ctx = function
      | CTG_vector ctyp -> codegen_vector ctx ctyp
      | CTG_tup ctyps -> codegen_tup ctx ctyps
      | CTG_list ctyp -> codegen_list ctx ctyp
  
      (*merge_file_docs merges generated header and implementation code into final C output, respecting header-generation settings.*)
    let merge_file_docs docs =
      let rec no_header impl = function
        | [] -> impl
        | Header doc :: docs -> no_header (impl ^^ doc ^^ twice hardline) docs
        | HeaderOnly _ :: docs -> no_header impl docs
        | Impl doc :: docs -> no_header (impl ^^ doc ^^ twice hardline) docs
      in
      let rec with_header hdr impl = function
        | [] -> (hdr, impl)
        | (Header doc | HeaderOnly doc) :: docs -> with_header (hdr ^^ doc ^^ twice hardline) impl docs
        | Impl doc :: docs -> with_header hdr (impl ^^ doc ^^ twice hardline) docs
      in
      if not Config.generate_header then (None, no_header empty docs)
      else (
        let hdr, impl = with_header empty empty docs in
        (Some hdr, impl)
      )

  let codegen_def ctx def=  (*2291*)(*It converts one jib definition to list of Document.t values*)
      let ctyps = cdef_ctyps def |> CTSet.elements in
      (*cdef_ctyps is a function that returns a set of ctyps for a given jib definition*)
      (*CTSet.elements converts the set to a list*)
      if List.exists is_polymorphic ctyps then (
  (*Checks if any of the types used are polymorphic (i.e., contain type variables like 'a, 'b, etc.).
  These should have been resolved (monomorphized) before code generation.*)
      let polymorphic_ctyps = List.filter is_polymorphic ctyps in
      c_error
        (Printf.sprintf "Found polymorphic types:\n%s\nwhile generating definition."
          (Util.string_of_list "\n" string_of_ctyp polymorphic_ctyps)
        )
    ) (*Filters to only keep the polymorphic types.  *)
    else (
      let deps = List.concat (List.map ctyp_dependencies ctyps) in
    (* For each used type in ctyps, compute its dependencies (i.e., other types it refers to).
      ctyp_dependencies: probably returns a list of dependent ctyps for each one.
      Flatten all dependency lists with List.concat.*)

      List.concat (List.map (codegen_ctg ctx) deps) @ codegen_def' ctx def
    (* Calls codegen_ctg for each dependency in deps to generate code for them.
  codegen_ctg might generate typedefs, enums, etc.
      
      Uses ctx to track context/config.*)
  (*So inside every jib definition there is a hidden C?
  Also when we turn compile_ast do we use AST or anf
  *)  
    
      )
  (*is_cdef_startup checks if a definition is a startup code block.*)
      let is_cdef_startup = function CDEF_aux (CDEF_startup _, _) -> true | _ -> false
  (*sgen_startup generates a C function call string for a given startup definition.*)
      let sgen_startup = function
        | CDEF_aux (CDEF_startup (id, _), _) -> Printf.sprintf "  startup_%s();" (sgen_function_id id)
        | _ -> assert false
    (*sgen_instr converts a single Sail instruction into a string of C code using the current context and function ID.*)
      let sgen_instr id ctx instr = Document.to_string (codegen_instr id ctx instr)
    (*is_cdef_finish (likely a bug) currently checks for startup definitions instead of finish definitions.*)
      let is_cdef_finish = function CDEF_aux (CDEF_startup _, _) -> true | _ -> false
    (*sgen_finish generates a C function call string for a finish code block (also currently looks for startup, probably unintended).*)
      let sgen_finish = function
        | CDEF_aux (CDEF_startup (id, _), _) -> Printf.sprintf "  finish_%s();" (sgen_function_id id)
        | _ -> assert false
    (*get_recursive_functions computes the set of functions that are recursive or mutually recursive by analyzing the call graph and strongly connected components.*)
      let get_recursive_functions cdefs =
        let graph = Jib_compile.callgraph cdefs in
        let rf = IdGraph.self_loops graph in
        (* Use strongly-connected components for mutually recursive functions *)
        List.fold_left (fun rf component -> match component with [_] -> rf | mutual -> mutual @ rf) rf (IdGraph.scc graph)
        |> IdSet.of_list

  (*Does this embed Ctype into AST while creating Jib?*)
  let jib_of_ast env effect_info ast =
      let module Jibc = Make (C_config 
      (*(struct
        let branch_coverage = Config.branch_coverage
        let assert_to_exception = Config.assert_to_exception
        let preserve_types = Config.preserve_types
      end)*) in
      let ctx = initial_ctx env effect_info in
      Jibc.compile_ast ctx ast      

  (*2336
  -c_ast_registers
  -get_unit_tests
  2351*)


  (*2353**)
  let compile_ast env effet_info basename ast = (*It includes 30 parts*)
    try
      (*Returns header: string option and impl: string*)
      (*-No runtime lifecycle functions
      .model_main should be reduced in here*)
      (*Converting ast to jib, cdefs is code and ctx is context  what context means and why necessary?*)
      let cdefs, ctx = jib_of_ast env effect_info ast in (*Converts the AST into intermediate code definitions (cdefs) and context (ctx).*)
      (* -cdefs = insert_heap_returns*) (*Inserts heap return handling into the code definitions based on the context.*)
      (*-recursive_functions = *) (*Extracts the set of recursive functions from the code definitions’ call graph.*)
      (*-cdefs = optimize*)(*Optimizes the code definitions, considering runtime system presence and recursive functions.*)
      (*-cdefs =List.map*)(*Flattens deeply nested definitions to a maximum depth of 100 to avoid compiler limits.*)
      let header_doc_opt, docs = List.map (codegen_def ctx) cdefs |> List.concat |> merge_file_docs in
      (*Generates C code documents and an optional header document from code definitions.*)
      (*List.map mapping the function (codegen_def ctx) to the list cdefs 
      cdefs are list of core language definitions in jib that will be compiled into C
      So codefen function compiles one definition to list of Document.t valies pretty print chuncks of C code
      1,Step: code_docs: Document.t list list where each inner list is the C Code for a single Sail definition
      2.Flattens the list so it is just Document.t list a flat list of all generated C code blocks
      3.This is a helper function that takes a list of code "documents" (Document.t list) and:
      Splits them into two groups:
      Header content: declarations that go into a .h file (e.g., prototypes, extern declarations, #defines, type aliases).
      Implementation content: function definitions, global variables, etc. that go into the .c file.*)
      (*
      - coverage_include, coverage_hook_header, coverage_hook 
      - preamble
      - exception_type 
      - exn_boilerplate =
      - letbind_initializers =
      - letbind_finalizers =
      - let startup cdefs = 
      - let finish cdefs = 
      - let early_regs = 
      - let regs = 
      - let register_init_clear (id, ctyp, instrs) =
      - let init_config_id = mk_id "__InitConfig" in
      - let model_init =
      - let model_fini =
      - let model_pre_exit =
      *)
      

      (*
      -What is codegen_def for
      -merge_file_docs
      -doc: Output c document
      -header_doc_opt:optinonal header file doc we dont have
      -No header
      -No error handling
      *)


      let model_main =
          [
            Printf.sprintf "%sint model_main(int argc, char *argv[])" (static ());
            "{";
            "  model_init();";
            "  if (process_arguments(argc, argv)) exit(EXIT_FAILURE);";
            Printf.sprintf "  %s(UNIT);" (sgen_function_id (mk_id "main"));
            "  model_fini();";
            "  model_pre_exit();";
            "  return EXIT_SUCCESS;";
            "}";
          ]
          |> List.map string |> separate hardline
      in

        (*-unit_test
        -unit_test_defs
        -model_test*)

      let actual_main =
        let extra_pre =
          List.filter_map
            (function CDEF_aux (CDEF_pragma ("c_in_main", arg), _) -> Some ("  " ^ arg) | _ -> None)
            cdefs
        in
        let extra_post =
          List.filter_map
            (function CDEF_aux (CDEF_pragma ("c_in_main_post", arg), _) -> Some ("  " ^ arg) | _ -> None)
            cdefs
        in
        separate hardline
          ( if Config.no_main then []
            else
              List.map string
                (["int main(int argc, char *argv[])"; "{"; "  int retcode;"]
                @ extra_pre @ ["  retcode = model_main(argc, argv);"] @ extra_post @ ["  return retcode;"; "}"]
                )
          )
      in

      let header =
        Option.map
          (fun header ->
            string "#pragma once" ^^ hlhl ^^ preamble true ^^ hlhl ^^ header ^^ hardline ^^ end_extern_cpp ^^ hardline
            |> Document.to_string
          )
          header_doc_opt
      in (*header is the first element of the return tuple*)
      ( header,
        Document.to_string
          (preamble false
          ^^ (if Config.generate_header then hardline ^^ Printf.ksprintf string "#include \"%s.h\"" basename else empty)
          ^^ hlhl ^^ docs ^^ hlhl
          ^^ ( if not Config.no_rts then
                model_init ^^ hlhl ^^ model_fini ^^ hlhl ^^ model_pre_exit ^^ hlhl ^^ model_main ^^ hlhl
              else empty
            )
          ^^ unit_test_defs ^^ hlhl ^^ model_test ^^ hlhl ^^ actual_main ^^ hardline ^^ end_extern_cpp ^^ hardline
          )
      )      
    with Type_error.Type_error (l, err) ->
      c_error ~loc:l ("Unexpected type error when compiling to C:\n" ^ fst (Type_error.string_of_type_error err))     
end