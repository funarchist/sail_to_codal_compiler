(****************************************************************************)
(* JIB Output Backend                                                      *)
(* Converts Sail AST to JIB and outputs the JIB representation            *)
(****************************************************************************)

open Libsail

open Ast
open Ast_util (*string_of_id comes from here*)
open Ast_defs
open Jib
open Jib_compile
open Jib_util
open Type_check

(*
open Jib_visitor
open PPrint
open Value2
module Document = Pretty_print_sail.Document

open Anf

module Big_int = Nat_big_num
*)
let c_error ?loc:(l = Parse_ast.Unknown) message = raise (Reporting.err_general l ("\nC backend: " ^ message))

(*Converting sail types through C_config*)


let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))



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

module C_config (Opts : sig
    val branch_coverage : out_channel option
    val assert_to_exception : bool
    val preserve_types : IdSet.t
  end) : CONFIG = struct
    (* Minimal: return a basic type for simple cases *)
    let rec convert_typ ctx typ =
      let (Typ_aux (typ_aux,l) as typ) = Env.expand_synonyms ctx.local_env typ in
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
      
      (*This partid for range types-range(0,31), atom('n) atom types and implicit('n)
      type, in here it handles parametrized integers through range type system
      
      *)
      
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

 (*    Absence of this part is "No C type for type bitvector('n)" which is also manifests as 
      "Internal error: Unreachable code (at src/lib/jib_compile.ml line 2390):
      ./riscv_types_minimal.sail:33.0-66.1:
      33 |mapping reg_abi_name_raw : bits(5) <-> string = {
         |^--------------------------------------------------
         id = bitvector and n=5
         codal is maybe bit[5] or sth
         JIB compiler assumes C_config can handle all Sail types

         "
         *)
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
  
    (* No literal/aval optimizations *)
    let optimize_anf _ aexp = aexp
  
    (* Default stubs / constants for CONFIG flags *)
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
  end


module IdMap = Map.Make (struct
  type t = id
  let compare = Id.compare
end)

type union_clause_info = {
  uc_constructor : id;  (*RTYPE*)
  uc_args : typ list;    (*[Typ_regidx; Typ_regidx; Typ_regidx; Typ_rop];, additional for enum types*)
  uc_loc : Parse_ast.l;
}

(*This structural info will replace string based heuristics when generating
use xpr_all as ...... like how many register will there be such as for immediate type there is only 2
or assembly{ } ordering or binary 


*)

type union_info = union_clause_info list IdMap.t

let typ_tuple_elems (typ : typ) =
  match typ with
  | Typ_aux (Typ_tuple typs, _) -> typs
  | _ -> [typ]

let add_union_clause (map : union_info) (union_id : id) (clause : type_union) =
  let Tu_aux (tu_aux, _) = clause in
  match tu_aux with
  | Tu_ty_id (clause_typ, constructor_id) ->
      let args = typ_tuple_elems clause_typ in
      let loc = typ_loc clause_typ in
      let clause_info = { uc_constructor = constructor_id; uc_args = args; uc_loc = loc } in
      let existing = match IdMap.find_opt union_id map with Some clauses -> clauses | None -> [] in
      IdMap.add union_id (clause_info :: existing) map

let collect_union_clauses defs =
  let handle_def acc = function
    | DEF_aux (DEF_type (TD_aux (TD_variant (union_id, _, clauses, _), _)), _) ->
        List.fold_left (fun m clause -> add_union_clause m union_id clause) acc clauses
    | DEF_aux (DEF_scattered (SD_aux (SD_unioncl (union_id, clause), _)), _) ->
        add_union_clause acc union_id clause
    | DEF_aux (DEF_scattered (SD_aux (SD_variant (_, _), _)), _) -> acc
    | DEF_aux (_, _) -> acc
  in
  List.fold_left handle_def IdMap.empty defs

type enum_literals = id list IdMap.t

let collect_enum_literals defs =
  let handle_def acc = function
    | DEF_aux (DEF_type (TD_aux (TD_enum (enum_id, members, _), _)), _) ->
        IdMap.add enum_id members acc
    | DEF_aux (DEF_scattered (SD_aux (SD_enumcl (enum_id, member), _)), _) ->
        let existing = match IdMap.find_opt enum_id acc with Some members -> members | None -> [] in
        IdMap.add enum_id (member :: existing) acc
    | DEF_aux (DEF_scattered (SD_aux (SD_enum _, _)), _) -> acc
    | DEF_aux (_, _) -> acc
  in
  List.fold_left handle_def IdMap.empty defs

(* Collect mapping definitions (encdec, mnemonic mappings, etc.) *)
type 'a mapping_info = {
  mi_id : id;
  mi_clauses : 'a mapcl list;
}

type 'a mapping_collection = 'a mapping_info IdMap.t  (* map from mapping ID to its info *)

let collect_mappings defs =
  let handle_def acc = function
    | DEF_aux (DEF_mapdef (MD_aux (MD_mapping (map_id, _, mapcls), _)), _) ->
        (* Store mapping with its clauses *)
        let mapping_info = { mi_id = map_id; mi_clauses = mapcls } in
        IdMap.add map_id mapping_info acc
    | DEF_aux (DEF_scattered (SD_aux (SD_mapcl (map_id, mapcl), _)), _) ->
        (* Handle scattered mapping clauses - append to existing or create new *)
        let existing = match IdMap.find_opt map_id acc with
          | Some info -> { info with mi_clauses = mapcl :: info.mi_clauses }
          | None -> { mi_id = map_id; mi_clauses = [mapcl] }
        in
        IdMap.add map_id existing acc
    | DEF_aux (_, _) -> acc
  in
  List.fold_left handle_def IdMap.empty defs


module Codalgen (Config : CODALGEN_CONFIG) = struct
  
  (***)
  (* Convert Sail AST to JIB intermediate representation *)
  (*Creating instance of jib compiler*)
  (*Initializing context with env and effect info*)
  (*Compiling ast to jib definitions*)  
  let jib_of_ast env effect_info ast =
    let module Jibc = Make (C_config (struct
      let branch_coverage = Config.branch_coverage
      let assert_to_exception = Config.assert_to_exception
      let preserve_types = Config.preserve_types
    end)) in
    let ctx = initial_ctx env effect_info in
    Jibc.compile_ast ctx ast


  (* Convert JIB operations to string representation *)
  let string_of_op = function
    | Iadd -> "add"
    | Isub -> "sub"
    | Ilt -> "lt"
    | Ilteq -> "lteq"
    | Igt -> "gt"
    | Igteq -> "gteq"
    | Eq -> "eq"
    | Neq -> "neq"
    | Band -> "and"
    | Bor -> "or"
    | Bnot -> "not"
    | Bvadd -> "bvadd"
    | Bvsub -> "bvsub"
    | Bvand -> "bvand"
    | Bvor -> "bvor"
    | Bvnot -> "bvnot"
    | Bvxor -> "bvxor"
    | List_hd -> "list_hd"
    | List_tl -> "list_tl"
    | List_is_empty -> "list_is_empty"
    | Ite -> "ite"
    | Get_abstract -> "get_abstract"
    | String_eq -> "string_eq"
    | Index _ -> "index"
    | Unsigned _ -> "unsigned"
    | Signed _ -> "signed"
    | Concat -> "concat"
    | Zero_extend _ -> "zero_extend"
    | Sign_extend _ -> "sign_extend"
    | Slice _ -> "slice"
    | Sslice _ -> "sslice"
    | Set_slice -> "set_slice"
    | Replicate _ -> "replicate"
    | Bvaccess -> "bvaccess"
    
  (* Convert JIB types to string representation *)
  let string_of_ctyp = function
    | CT_unit -> "void"
    | CT_bit -> "bit"
    | CT_bool -> "bool"
    | CT_fbits _ -> "bits"
    | CT_sbits _ -> "bits"
    | CT_fint _ -> "int"
    | CT_constant _ -> "int"
    | CT_lint -> "int"
    | CT_lbits -> "bits"
    | CT_tup _ -> "tuple"
    | CT_struct (id, _) -> "struct_" ^ (string_of_id id)
    | CT_enum id -> "enum_" ^ (string_of_id id)
    | CT_variant (id, _) -> "variant_" ^ (string_of_id id)
    | CT_list _ -> "list"
    | CT_vector _ -> "vector"
    | CT_fvector (_, _) -> "vector"
    | CT_string -> "string"
    | CT_real -> "real"
    | CT_json -> "json"
    | CT_json_key -> "json_key"
    | CT_ref ctyp -> "ref_" ^ (string_of_ctyp ctyp)
    | CT_float _ -> "float"
    | CT_rounding_mode -> "rounding_mode"
    | CT_memory_writes -> "memory_writes"
    | CT_poly _ -> "poly"

  (* Helper function to check if string contains substring *)
  let string_contains str substr =
    try
      let len = String.length substr in
      let rec check i =  (*Definition of Local recursive member function*)
        if i + len > String.length str then false
        else if String.sub str i len = substr then true
        else check (i + 1)
      in
      check 0 (*Call to defined function*)
    with
    | _ -> false   (*If substring is not found any exception that is raised will be evaluated to Fail*)

  

(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)   
(*This evaluated parts will be in switch(op) result= ....*)
  (* Generate operation for R-type instructions *)
  let generate_operation func_name =
    let name_lower = String.lowercase_ascii func_name in
    match name_lower with
    | name when string_contains name "add" -> "src1 + src2"
    | name when string_contains name "sub" -> "src1 - src2"
    | name when string_contains name "and" -> "src1 & src2"
    | name when string_contains name "or" -> "src1 | src2"
    | name when string_contains name "xor" -> "src1 ^ src2"
    | name when string_contains name "sll" -> "src1 << src2"
    | name when string_contains name "srl" -> "src1 >> src2"
    | name when string_contains name "sra" -> "(int32)src1 >> src2"
    | name when string_contains name "slt" -> "((int32)src1 < (int32)src2) ? 1 : 0"
    | name when string_contains name "sltu" -> "(src1 < src2) ? 1 : 0"
    | _ -> "/* Operation */"

  (* Generate operation for I-type instructions *)
  let generate_itype_operation func_name =
    let name_lower = String.lowercase_ascii func_name in
    match name_lower with
    | name when string_contains name "addi" -> "src1 + immediate"
    | name when string_contains name "andi" -> "src1 & immediate"
    | name when string_contains name "ori" -> "src1 | immediate"
    | name when string_contains name "xori" -> "src1 ^ immediate"
    | name when string_contains name "slti" -> "((int32)src1 < immediate) ? 1 : 0"
    | name when string_contains name "sltiu" -> "((uint32)src1 < (uint32)immediate) ? 1 : 0"
    | _ -> "/* Operation */"

  (* Generate condition for B-type instructions *)
  let generate_btype_condition func_name =
    let name_lower = String.lowercase_ascii func_name in
    match name_lower with
    | name when string_contains name "beq" -> "(src1 == src2) ? 1 : 0"
    | name when string_contains name "bne" -> "(src1 != src2) ? 1 : 0"
    | name when string_contains name "blt" -> "((int32)src1 < (int32)src2) ? 1 : 0"
    | name when string_contains name "bge" -> "((int32)src1 >= (int32)src2) ? 1 : 0"
    | name when string_contains name "bltu" -> "((uint32)src1 < (uint32)src2) ? 1 : 0"
    | name when string_contains name "bgeu" -> "((uint32)src1 >= (uint32)src2) ? 1 : 0"
    | _ -> "/* Condition */"

  (* Generate operation for U-type instructions *)
  let generate_utype_operation func_name =
    let name_lower = String.lowercase_ascii func_name in
    match name_lower with
    | name when string_contains name "lui" -> "(int32)imm << 12"
    | name when string_contains name "auipc" -> "current_pc + ((int32)imm << 12)"
    | _ -> "/* Operation */"






  (* Convert RISC-V register definitions to Codal format *)
  let generate_register_definitions () =
    let registers = [
      (0, "x0", "zero");
      (1, "x1", "ra");
      (2, "x2", "sp");
      (3, "x3", "gp");
      (4, "x4", "tp");
      (5, "x5", "t0");
      (6, "x6", "t1");
      (7, "x7", "t2");
      (8, "x8", "fp");
      (9, "x9", "s1");
      (10, "x10", "a0");
      (11, "x11", "a1");
      (12, "x12", "a2");
      (13, "x13", "a3");
      (14, "x14", "a4");
      (15, "x15", "a5");
      (16, "x16", "a6");
      (17, "x17", "a7");
      (18, "x18", "s2");
      (19, "x19", "s3");
      (20, "x20", "s4");
      (21, "x21", "s5");
      (22, "x22", "s6");
      (23, "x23", "s7");
      (24, "x24", "s8");
      (25, "x25", "s9");
      (26, "x26", "s10");
      (27, "x27", "s11");
      (28, "x28", "t3");
      (29, "x29", "t4");
      (30, "x30", "t5");
      (31, "x31", "t6");
    ] in
    
    let register_elements = List.map (fun (num, reg_name, alias) ->
      if num = 0 then
        Printf.sprintf "element %s\n{\n    assembly{STRINGIZE(%s)};\n    binary  {%d:bit[5]};\n    return{%d};\n};\n\nelement %s_alias : assembler_alias(%s)\n{\n    assembly { \"%s\" };\n    binary { %d:bit[5] };\n};" 
          reg_name reg_name num num reg_name reg_name alias num
      else
        Printf.sprintf "DEF_REG_ALIAS(%d, \"%s\")       // %s" num alias reg_name
    ) registers in
    
    let register_sets = [
      "set xpr_general : register_class(rf_xpr);";
      "set xpr_all;";
      "set xpr_all += xpr_general, x_0, x_0_alias;";
    ] in
    
    String.concat "\n" (register_elements @ [""] @ register_sets)

  (* Convert immediate value definitions to Codal format *)
  let generate_immediate_definitions () =
    let immediates = [
      ("uimm5", "unsigned 5-bit immediate", "IMM5_W", "unsigned attribute bit[IMM5_W] value");
      ("simm12", "signed 12-bit immediate", "IMM12_W", "signed attribute bit[IMM12_W] value");
      ("uimm20", "unsigned 20-bit immediate", "IMM20_W", "unsigned attribute bit[IMM20_W] value");
    ] in
    
    List.map (fun (name, comment, _width, attr) ->
      Printf.sprintf "element %s       // %s\n{\n    %s;\n\n    assembly {value};\n    binary {value};\n\n    return {value};\n};" 
        name comment attr
    ) immediates

  (* Convert address operands to Codal format *)
  let generate_address_operands () =
    let address_ops = [
      ("relative_addr12", "signed attribute bit[12] addr12", "HALF_W_ALIGN");
      ("relative_addr20", "signed attribute bit[20] addr20", "HALF_W_ALIGN");
    ] in
    
    List.map (fun (name, attr, align) ->
      Printf.sprintf "element %s\n{\n    %s\n    {\n        label = true;\n        encoding = (addr%d - current_address) >> %s;\n        decoding = ((int%d)addr%d << %s) + current_address;\n    };\n    assembly {addr%d};\n    binary{addr%d};\n    return{(uint32)addr%d << %s};\n};" 
        name attr (String.length name - 2) align (String.length name - 1) (String.length name - 2) align (String.length name - 2) (String.length name - 2) (String.length name - 2) align
    ) address_ops


  (* Structure to store extracted opcode information from encdec mappings *)
  type opcode_info = {
    oi_constructor : id;  (* RTYPE, ITYPE, etc. *)
    oi_enum_value : id;    (* ADD, SUB, etc. *)
    oi_bit_pattern : string;  (* Full opcode bit pattern as string for now *)
    oi_func7 : string option;  (* func7 bits (7 bits) *)
    oi_func3 : string option;  (* func3 bits (3 bits) *)
    oi_opcode : string option;  (* opcode bits (7 bits) *)
    oi_computed_value : string option;  (* Computed full opcode value *)
  }

  (* Structure to store mnemonic information *)
  type mnemonic_info = {
    mi_enum_value : id;
    mi_mnemonic : string;
  }

  (* it takes argument in type cdef_aux list and returns a tuple of strings *)
  let jib_to_codal union_info enum_info (mapping_info : 'a mapping_collection) (cdefs : cdef_aux list) =
    (* Debug: print what mappings were collected *)
    Printf.eprintf "=== Debug: Collected %d mappings ===\n" (IdMap.cardinal mapping_info);
    IdMap.iter (fun id info ->
      Printf.eprintf "  Mapping '%s' with %d clauses\n" (string_of_id id) (List.length info.mi_clauses)
    ) mapping_info;
    Printf.eprintf "=================================\n";
    
    (* Find and parse encdec mapping to extract opcode patterns *)
    let encdec_id = mk_id "encdec" in
    let encdec_mapping = match IdMap.find_opt encdec_id mapping_info with
      | Some info -> 
          Printf.eprintf "✓ Found 'encdec' mapping with %d clauses\n" (List.length info.mi_clauses);
          Some info
      | None -> 
          Printf.eprintf "✗ ERROR: 'encdec' mapping not found!\n";
          None
    in
    
    (* Helper: Extract bit literal value *)
    let extract_bit_literal (mpexp : 'b mpexp) : (string * int) option =
      match mpexp with
      | MPat_aux (MPat_pat (MP_aux (MP_lit (L_aux (L_bin bits, _)), _)), _) ->
          (* Parse binary literal: 0b... *)
          (try
             let value = int_of_string ("0b" ^ bits) in
             Some (bits, value)
           with _ -> None)
      | MPat_aux (MPat_pat (MP_aux (MP_lit (L_aux (L_hex hex, _)), _)), _) ->
          (* Parse hex literal: 0x... *)
          (try
             let value = int_of_string ("0x" ^ hex) in
             Some (hex, value)
           with _ -> None)
      | MPat_aux (MPat_pat (MP_aux (MP_lit (L_aux (L_num num, _)), _)), _) ->
          (* Parse numeric literal *)
          (try
             let value = Big_int.to_int num in
             Some (string_of_int value, value)
           with _ -> None)
      | _ -> None
    in
    
    (* Helper: Extract bit pattern from right-hand side expression/pattern *)
    let extract_bit_pattern_from_mpexp (mpexp : 'b mpexp) : string option =
      match extract_bit_literal mpexp with
      | Some (bits_str, _) -> Some ("0b" ^ bits_str)
      | None ->
          match mpexp with
          | MPat_aux (MPat_pat (MP_aux (MP_app (id, _), _)), _) ->
              (* Handle function calls like encdec_reg, encdec_uop, etc. *)
              let func_name = string_of_id id in
              if func_name = "encdec_reg" || func_name = "encdec_uop" || 
                 func_name = "encdec_iop" || func_name = "encdec_bop" ||
                 func_name = "encdec_sop" then
                (* These are encoding functions - we'll need to resolve them later *)
                Some ("<" ^ func_name ^ ">")
              else
                None
          | _ -> None
    in
    
    (* Helper: Extract pattern parts from concatenation and compute opcode *)
    (* Returns: (all_parts_list, (func7, func3, opcode)) *)
    let rec extract_pattern_parts_from_concat (mpexp : 'b mpexp) : (string list * (int option * int option * int option)) =
      match mpexp with
      | MPat_aux (MPat_pat (MP_aux (MP_app (id, [left; right]), _)), annot) ->
          let func_name = string_of_id id in
          if func_name = "@" then
            (* Concatenation - recurse on both sides and collect all literals *)
            (* Wrap left and right mpat values into mpexp using the same annotation *)
            let (left_parts, _) = extract_pattern_parts_from_concat (MPat_aux (MPat_pat left, annot)) in
            let (right_parts, _) = extract_pattern_parts_from_concat (MPat_aux (MPat_pat right, annot)) in
            (* Combine parts *)
            let all_parts = left_parts @ right_parts in
            (* For RTYPE: pattern is func7 @ rs2 @ rs1 @ func3 @ rd @ opcode *)
            (* We need to identify: first 7-bit = func7, 3-bit = func3, last 7-bit = opcode *)
            let all_literals = List.filter_map (fun part ->
              (* Try to parse as binary literal *)
              try
                if String.length part >= 2 && String.sub part 0 2 = "0b" then
                  let bits = String.sub part 2 (String.length part - 2) in
                  Some (bits, int_of_string ("0b" ^ bits))
                else None
              with _ -> None
            ) all_parts in
            
            (* Identify func7, func3, opcode by position and bit width *)
            let func7_opt = 
              (* First 7-bit literal is func7 *)
              (match List.find_opt (fun (bits, _) -> String.length bits = 7) all_literals with
               | Some (_, value) -> Some value
               | None -> None)
            in
            let func3_opt =
              (* 3-bit literal is func3 (typically after registers) *)
              (match List.find_opt (fun (bits, _) -> String.length bits = 3) all_literals with
               | Some (_, value) -> Some value
               | None -> None)
            in
            let opcode_opt =
              (* Last 7-bit literal is opcode *)
              (match List.rev all_literals |> List.find_opt (fun (bits, _) -> String.length bits = 7) with
               | Some (_, value) -> Some value
               | None -> None)
            in
            
            (all_parts, (func7_opt, func3_opt, opcode_opt))
          else
            (match extract_bit_pattern_from_mpexp mpexp with
             | Some s -> ([s], (None, None, None))
             | None -> ([], (None, None, None)))
      | _ ->
          (match extract_bit_literal mpexp with
           | Some (bits_str, value) ->
               let len = String.length bits_str in
               let func7_opt = if len = 7 then Some value else None in
               let func3_opt = if len = 3 then Some value else None in
               let opcode_opt = if len = 7 then Some value else None in
               ([bits_str], (func7_opt, func3_opt, opcode_opt))
           | None -> ([], (None, None, None)))
    in
    
    (* Helper: Convert integer to binary string with specified width *)
    let int_to_binary_string value width =
      let rec to_bin n w acc =
        if w <= 0 then acc
        else to_bin (n lsr 1) (w - 1) (string_of_int (n land 1) ^ acc)
      in
      "0b" ^ to_bin value width ""
    in
    
    (* Helper: Compute full opcode value from parts *)
    let compute_opcode_value (func7_opt, func3_opt, opcode_opt) constructor_name : string option =
      match (func7_opt, func3_opt, opcode_opt) with
      | (Some func7, Some func3, Some opc) when constructor_name = "RTYPE" ->
          (* RTYPE: func7 (7 bits) @ func3 (3 bits) @ opcode (7 bits) = 17 bits total *)
          let full_value = (func7 lsl 10) lor (func3 lsl 7) lor opc in
          Some (int_to_binary_string full_value 17)
      | (None, Some func3, Some opc) when constructor_name = "ITYPE" || constructor_name = "BTYPE" || constructor_name = "STORE" ->
          (* ITYPE/BTYPE/STORE: func3 (3 bits) @ opcode (7 bits) = 10 bits total *)
          let full_value = (func3 lsl 7) lor opc in
          Some (int_to_binary_string full_value 10)
      | (Some func7, Some func3, Some opc) when constructor_name = "SHIFTIOP" ->
          (* SHIFTIOP: func7 (7 bits) @ func3 (3 bits) @ opcode (7 bits) = 17 bits total *)
          let full_value = (func7 lsl 10) lor (func3 lsl 7) lor opc in
          Some (int_to_binary_string full_value 17)
      | (None, None, Some opc) when constructor_name = "UTYPE" || constructor_name = "JAL" ->
          (* UTYPE/JAL: opcode (7 bits) only *)
          Some (int_to_binary_string opc 7)
      | _ -> None
    in
    
    (* Helper: Resolve helper mapping (encdec_uop, encdec_bop, etc.) to get opcode value *)
    let resolve_helper_mapping (helper_name : string) (enum_value_id : id) : int option =
      (* Look for mapping like encdec_uop, encdec_bop, etc. *)
      let helper_id = mk_id helper_name in
      match IdMap.find_opt helper_id mapping_info with
      | Some info ->
          (* Find the clause that maps enum_value_id to a bit pattern *)
          let rec find_mapping = function
            | [] -> None
            | mapcl :: rest ->
                match mapcl with
                | MCL_aux (MCL_bidir (left_mpexp, right_mpexp), _) ->
                    (* Check if left side matches enum_value_id *)
                    (match left_mpexp with
                     | MPat_aux (MPat_pat (MP_aux (MP_id id, _)), _) ->
                         if Id.compare id enum_value_id = 0 then
                           (* Extract bit value from right side *)
                           (match extract_bit_literal right_mpexp with
                            | Some (_, value) -> Some value
                            | None -> None)
                         else find_mapping rest
                     | _ -> find_mapping rest)
                | _ -> find_mapping rest
          in
          find_mapping info.mi_clauses
      | None -> None
    in
    
    (* Parse encdec mapping clauses to extract opcode information *)
    let parse_encdec_clause (mapcl : 'b mapcl) : opcode_info option =
      match mapcl with
      | MCL_aux (MCL_bidir (left_mpexp, right_mpexp), _) ->
          (* Extract constructor and enum value from left pattern *)
          let extract_from_pattern (mpexp : 'b mpexp) =
            match mpexp with
            | MPat_aux (MPat_pat (MP_aux (MP_app (constructor_id, args), _)), _) ->
                (* Get the last argument which should be the enum value *)
                (match args with
                 | [] -> None
                 | args_list ->
                     let last_arg = List.nth args_list (List.length args_list - 1) in
                     match last_arg with
                     | MP_aux (MP_id enum_value_id, _) ->
                         Some (constructor_id, enum_value_id)
                     | _ -> None)
        | _ -> None
          in
          (match extract_from_pattern left_mpexp with
           | Some (constructor_id, enum_value_id) ->
               (* Extract pattern parts and compute opcode value *)
               let (pattern_parts, (func7_opt, func3_opt, opcode_opt)) = 
                 extract_pattern_parts_from_concat right_mpexp in
               
               (* Check if we need to resolve helper mappings (e.g., encdec_uop, encdec_bop) *)
               (* For UTYPE: pattern is imm @ rd @ encdec_uop(op) *)
               (* For BTYPE: pattern includes encdec_bop(op) *)
               let constructor_name = string_of_id constructor_id in
               let resolved_func3_opt = 
                 (* If func3 is missing but we have a helper mapping, resolve it *)
                 if func3_opt = None then
                   match constructor_name with
                   | "UTYPE" -> 
                       (* UTYPE uses encdec_uop which gives 7-bit opcode, not func3 *)
                       None
                   | "BTYPE" ->
                       (* BTYPE uses encdec_bop which gives 3-bit func3 *)
                       resolve_helper_mapping "encdec_bop" enum_value_id
                   | "ITYPE" ->
                       (* ITYPE uses encdec_iop which gives 3-bit func3 *)
                       resolve_helper_mapping "encdec_iop" enum_value_id
                   | "STORE" ->
                       (* STORE might use encdec_sop *)
                       resolve_helper_mapping "encdec_sop" enum_value_id
                   | "SHIFTIOP" ->
                       (* SHIFTIOP uses encdec_sop which gives 3-bit func3 *)
                       resolve_helper_mapping "encdec_sop" enum_value_id
                   | _ -> None
                 else func3_opt
               in
               
               let resolved_opcode_opt =
                 (* If opcode is missing, try to resolve from helper mapping *)
                 if opcode_opt = None then
                   match constructor_name with
                   | "UTYPE" ->
                       (* UTYPE uses encdec_uop which gives 7-bit opcode *)
                       resolve_helper_mapping "encdec_uop" enum_value_id
                   | _ -> opcode_opt
                 else opcode_opt
               in
               
               let bit_pattern = if pattern_parts = [] then "TODO" 
                                else String.concat " " pattern_parts in
               let computed_value = compute_opcode_value (func7_opt, resolved_func3_opt, resolved_opcode_opt) constructor_name in
               
               (* Extract func7, func3, opcode as strings *)
               let func7_str = match func7_opt with
                 | Some v -> Some (int_to_binary_string v 7)
                 | None -> None
               in
               let func3_str = match resolved_func3_opt with
                 | Some v -> Some (int_to_binary_string v 3)
                 | None -> None
               in
               let opcode_str = match resolved_opcode_opt with
                 | Some v -> Some (int_to_binary_string v 7)
                 | None -> None
               in
               
               Some { oi_constructor = constructor_id; 
                      oi_enum_value = enum_value_id; 
                      oi_bit_pattern = bit_pattern;
                      oi_func7 = func7_str;
                      oi_func3 = func3_str;
                      oi_opcode = opcode_str;
                      oi_computed_value = computed_value }
           | None -> None)
      | _ -> None
    in
    
    (* Extract all opcodes from encdec mapping *)
    let extracted_opcodes = match encdec_mapping with
      | Some info ->
          let opcodes = List.filter_map parse_encdec_clause info.mi_clauses in
          (* Debug: print extracted opcodes *)
          Printf.eprintf "Extracted %d opcodes from encdec mapping\n" (List.length opcodes);
          List.iter (fun opc ->
            Printf.eprintf "  %s.%s -> %s\n" 
              (string_of_id opc.oi_constructor)
              (string_of_id opc.oi_enum_value)
              opc.oi_bit_pattern
          ) opcodes;
          opcodes
      | None -> []
    in
    
    (* Parse mnemonic mappings (e.g., rtype_mnemonic, utype_mnemonic) *)
    let parse_mnemonic_clause (mapcl : 'b mapcl) : mnemonic_info option =
      match mapcl with
      | MCL_aux (MCL_bidir (left_mpexp, right_mpexp), _) ->
          (* Left: enum value (e.g., ADD), Right: string literal (e.g., "add") *)
          let extract_enum = function
            | MPat_aux (MPat_pat (MP_aux (MP_id enum_id, _)), _) -> Some enum_id
            | _ -> None
          in
          let extract_string = function
            | MPat_aux (MPat_pat (MP_aux (MP_lit (L_aux (L_string s, _)), _)), _) -> Some s
            | _ -> None
          in
          (match (extract_enum left_mpexp, extract_string right_mpexp) with
           | (Some enum_id, Some mnemonic) ->
               Some { mi_enum_value = enum_id; mi_mnemonic = mnemonic }
           | _ -> None)
      | _ -> None
    in
    
    let parse_mnemonic_mapping (map_id : id) (info : 'b mapping_info) : (id * mnemonic_info list) option =
      (* Check if this is a mnemonic mapping (ends with _mnemonic) *)
      let map_name = string_of_id map_id in
      let suffix = "_mnemonic" in
      let suffix_len = String.length suffix in
      let name_len = String.length map_name in
      if name_len < suffix_len then None
      else if String.sub map_name (name_len - suffix_len) suffix_len <> suffix then None
      else
        let mnemonics = List.filter_map parse_mnemonic_clause info.mi_clauses in
        if mnemonics = [] then None else Some (map_id, mnemonics)
    in
    
    (* Extract all mnemonic mappings *)
    let extracted_mnemonics = 
      let mnemonics = IdMap.fold (fun map_id info acc ->
        match parse_mnemonic_mapping map_id info with
        | Some (id, mnemonics) -> (id, mnemonics) :: acc
        | None -> acc
      ) mapping_info [] in
      (* Debug: print extracted mnemonics *)
      Printf.eprintf "Extracted %d mnemonic mappings\n" (List.length mnemonics);
      List.iter (fun (map_id, mnemonics_list) ->
        Printf.eprintf "  %s: %d entries\n" (string_of_id map_id) (List.length mnemonics_list);
        List.iter (fun m ->
          Printf.eprintf "    %s -> \"%s\"\n" (string_of_id m.mi_enum_value) m.mi_mnemonic
        ) mnemonics_list
      ) mnemonics;
      mnemonics
    in
    
    (* Parse assembly mappings - these are typically "mapping clause assembly = ..." *)
    (* For now, we'll extract them but use mnemonic mappings for assembly syntax *)
    (* Assembly mappings are more complex as they contain formatted strings *)
    (* We can enhance this later to parse the actual assembly format strings *)
    
    (* Helper: Extract enum type from union clause arguments (typically the last arg) *)
    let extract_enum_type_from_clause (clause : union_clause_info) =
      match clause.uc_args with
      | [] -> None
      | args -> 
          (* The enum is typically the last argument *)
          let last_arg = List.nth args (List.length args - 1) in
          match last_arg with
          | Typ_aux (Typ_id enum_id, _) -> Some enum_id
          | _ -> None
    in
    
    (* Find the "ast" union type to identify instruction families *)
    let ast_union_id = mk_id "ast" in
    let ast_clauses = match IdMap.find_opt ast_union_id union_info with
      | Some clauses -> clauses
      | None -> []
    in

    (***************************************************************************************************************)
    (* Convert JIB CDEF to CodAL string representation *)
    (* Note: Instruction elements are now generated by generate_instruction_elements() from union clauses *)
    (* This function only handles non-instruction CDEFs (values, types, registers, etc.) *)
    let codal_cdef = function
      | CDEF_fundef (id, _return_id_opt, _args, _instrs) ->
          (* Instruction functions are now handled by generate_instruction_elements() *)
          (* Skip them here to avoid duplicate generation *)
          let func_name = string_of_id id in
          if func_name = "execute" then
            ""  (* execute function is handled by generate_instruction_elements() *)
          else
            ""  (* Other instruction functions are also handled by generate_instruction_elements() *)
            
      | CDEF_val (id, _tyvars, ctyps, ctyp, extern) ->
          let val_name = string_of_id id in
          let param_types = String.concat ", " (List.map string_of_ctyp ctyps) in
          let extern_str = match extern with
            | Some extern_name -> " = " ^ extern_name
            | None -> ""
          in
          Printf.sprintf "%s %s(%s)%s;" 
            (string_of_ctyp ctyp) val_name param_types extern_str
            
      | CDEF_type ctype_def ->
          "// Type definition: " ^ (match ctype_def with
            | CTD_enum (id, _ids) -> "enum " ^ (string_of_id id)
            | CTD_struct (id, _kids, _fields) -> "struct " ^ (string_of_id id)
            | CTD_variant (id, _kids, _fields) -> "variant " ^ (string_of_id id)
            | CTD_abbrev (id, _ctyp) -> "abbrev " ^ (string_of_id id)
            | CTD_abstract (id, _ctyp, _) -> "abstract " ^ (string_of_id id))
          
      | CDEF_register (id, ctyp, instrs) ->
          Printf.sprintf "register %s: %s {\n  %s\n}" 
            (string_of_name id) (string_of_ctyp ctyp) 
            (String.concat "\n  " (List.map string_of_instr instrs))
            
      | CDEF_let (n, bindings, instrs) ->
          let bindings_str = String.concat ", " (List.map (fun (id, ctyp) -> 
            Printf.sprintf "%s: %s" (string_of_id id) (string_of_ctyp ctyp)) bindings) in
          Printf.sprintf "let %d (%s) {\n  %s\n}" 
            n bindings_str (String.concat "\n  " (List.map string_of_instr instrs))
            
      | CDEF_startup (id, instrs) ->
          Printf.sprintf "startup %s {\n  %s\n}" 
            (string_of_id id) (String.concat "\n  " (List.map string_of_instr instrs))
            
      | CDEF_finish (id, instrs) ->
          Printf.sprintf "finish %s {\n  %s\n}" 
            (string_of_id id) (String.concat "\n  " (List.map string_of_instr instrs))
            
      | CDEF_pragma (name, str) ->
          Printf.sprintf "pragma %s: %s" name str
    in
    

 (*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)   
    (* Helper: Find mnemonic for an enum value in a specific family *)
    let find_mnemonic_for_enum constructor_name enum_value_id =
      (* Look for mnemonic mapping like rtype_mnemonic, utype_mnemonic, etc. *)
      let expected_mapping_name = (String.lowercase_ascii constructor_name) ^ "_mnemonic" in
      match List.find_opt (fun (map_id, _) -> 
        string_of_id map_id = expected_mapping_name
      ) extracted_mnemonics with
      | Some (_, mnemonics) ->
          (match List.find_opt (fun m -> Id.compare m.mi_enum_value enum_value_id = 0) mnemonics with
           | Some m -> Some m.mi_mnemonic
           | None -> None)
      | None -> None
    in
    
    (* Generate DEF_OPC calls for all instruction families *)
    let generate_def_opc_calls_for_family clause =
      match extract_enum_type_from_clause clause with
      | Some enum_id ->
          let enum_values = match IdMap.find_opt enum_id enum_info with
            | Some ids -> ids
            | None -> []
          in
          if enum_values = [] then ""
          else
            let constructor_name = string_of_id clause.uc_constructor in
            let family_prefix = String.uppercase_ascii constructor_name in
            let opc_defs = List.map (fun enum_value_id ->
              let op_name = string_of_id enum_value_id in
          let op_lower = String.lowercase_ascii op_name in
              (* Look up mnemonic from extracted mappings, fallback to lowercase enum name *)
              let mnemonic = match find_mnemonic_for_enum constructor_name enum_value_id with
                | Some m -> m
                | None -> op_lower
              in
              Printf.sprintf "DEF_OPC(%s, \"%s\", %s_%s)" 
                op_lower mnemonic family_prefix (String.uppercase_ascii op_name)
            ) enum_values in
        String.concat "\n" opc_defs
      | None -> ""
    in
    
    let generate_def_opc_calls () =
      let all_defs = List.map generate_def_opc_calls_for_family ast_clauses in
      let non_empty = List.filter (fun s -> s <> "") all_defs in
      String.concat "\n" non_empty
    in
    
    (* Generate opcode sets for all instruction families *)
    let generate_opc_set_for_family clause =
      match extract_enum_type_from_clause clause with
      | Some enum_id ->
          let enum_values = match IdMap.find_opt enum_id enum_info with
            | Some ids -> List.map string_of_id ids
            | None -> []
          in
          if enum_values = [] then ""
          else
            let constructor_name = string_of_id clause.uc_constructor in
            let constructor_lower = String.lowercase_ascii constructor_name in
            let opc_names = List.map (fun op -> "opc_" ^ String.lowercase_ascii op) enum_values in
            Printf.sprintf "set opc_%s = %s;" constructor_lower (String.concat ", " opc_names)
      | None -> ""
    in
    
    let generate_opc_set () =
      let all_sets = List.map generate_opc_set_for_family ast_clauses in
      let non_empty = List.filter (fun s -> s <> "") all_sets in
      String.concat "\n" non_empty
    in
    
    (* Helper: Determine operand names and types from union clause arguments *)
    let determine_operands (clause : union_clause_info) : (string * string) list =
      let constructor_name = string_of_id clause.uc_constructor in
      (* Filter out the enum type (last argument) and other non-operand types *)
      let args_without_enum = match clause.uc_args with
        | [] -> []
        | args -> 
            (* Remove last arg (enum type) *)
            let len = List.length args in
            if len > 0 then
              List.rev (List.tl (List.rev args))
            else []
      in
      
      (* Separate immediates from registers *)
      let _immediates = List.filter_map (fun (idx, typ) ->
        match typ with
        | Typ_aux (Typ_app (id, [A_aux (A_nexp _, _)]), _) when string_of_id id = "bits" ->
            Some (idx, typ)
        | _ -> None
      ) (List.mapi (fun i t -> (i, t)) args_without_enum) in
      
      let registers = List.filter_map (fun (idx, typ) ->
        match typ with
        | Typ_aux (Typ_id id, _) when string_of_id id = "regidx" ->
            Some (idx, typ)
        | _ -> None
      ) (List.mapi (fun i t -> (i, t)) args_without_enum) in
      
      (* Helper: find index in a list *)
      let find_index pred lst =
        let rec find i = function
          | [] -> None
          | x :: xs -> if pred x then Some i else find (i + 1) xs
        in
        find 0 lst
      in
      
      (* Classify each argument by type and position *)
      let classify_arg idx typ =
        match typ with
        | Typ_aux (Typ_id id, _) ->
            let type_name = string_of_id id in
            if type_name = "regidx" then
              (* Register operand - find position among registers only *)
              let reg_pos = find_index (fun (i, _) -> i = idx) registers in
              (match (constructor_name, reg_pos) with
               | ("RTYPE", Some 0) -> ("rs2", "xpr_all")
               | ("RTYPE", Some 1) -> ("rs1", "xpr_all")
               | ("RTYPE", Some 2) -> ("rd", "xpr_all")
               | ("BTYPE", Some 0) -> ("rs2", "xpr_all")
               | ("BTYPE", Some 1) -> ("rs1", "xpr_all")
               | ("STORE", Some 0) -> ("rs2", "xpr_all")
               | ("STORE", Some 1) -> ("rs1", "xpr_all")
               | ("JALR", Some 0) -> ("rs1", "xpr_all")
               | ("JALR", Some 1) -> ("rd", "xpr_all")
               | ("LOAD", Some 0) -> ("rs1", "xpr_all")
               | ("LOAD", Some 1) -> ("rd", "xpr_all")
               | ("ITYPE", Some 0) -> ("rs1", "xpr_all")
               | ("ITYPE", Some 1) -> ("rd", "xpr_all")
               | ("UTYPE", Some 0) | ("JAL", Some 0) -> ("rd", "xpr_all")
               | (_, Some 0) -> ("rd", "xpr_all")
               | (_, Some 1) -> ("rs1", "xpr_all")
               | (_, Some 2) -> ("rs2", "xpr_all")
               | _ -> ("reg" ^ string_of_int idx, "xpr_all"))
            else
              ("arg" ^ string_of_int idx, "xpr_all")
        | Typ_aux (Typ_app (id, [A_aux (A_nexp _, _)]), _) ->
            let type_name = string_of_id id in
            if type_name = "bits" then
              (* Immediate operand - determine type based on bit width and instruction type *)
              (match constructor_name with
               | "UTYPE" | "JAL" -> ("imm", "uimm20")
               | "BTYPE" -> ("imm", "relative_addr12")
               | "JALR" | "ITYPE" | "STORE" | "LOAD" -> ("imm", "simm12")
               | "SHIFTIOP" -> ("shamt", "uimm5")
               | _ -> ("imm", "simm12"))
            else
              ("arg" ^ string_of_int idx, "xpr_all")
        | _ -> ("arg" ^ string_of_int idx, "xpr_all")
      in
      
      List.mapi classify_arg args_without_enum
    in
    
    (* Generate instruction element for a family *)
    let generate_instruction_element (clause : union_clause_info) : string =
      let constructor_name = string_of_id clause.uc_constructor in
      let constructor_lower = String.lowercase_ascii constructor_name in
      
      (* Get enum values for this family *)
      let enum_values = match extract_enum_type_from_clause clause with
        | Some enum_id ->
            (match IdMap.find_opt enum_id enum_info with
             | Some ids -> ids
             | None -> [])
        | None -> []
      in
      
      if enum_values = [] then ""
      else
        (* Determine operands *)
        let operands = determine_operands clause in
        let use_decls = List.map (fun (name, _) -> name) operands in
        let _use_types = List.map (fun (_, codal_type) -> codal_type) operands in
        
        (* Group operands by type for use declarations *)
        let register_ops = List.filter_map (fun (name, typ) ->
          if typ = "xpr_all" then Some name else None
        ) operands in
        let immediate_ops = List.filter_map (fun (name, typ) ->
          if typ <> "xpr_all" then Some (name, typ) else None
        ) operands in
        
        (* Generate use declarations *)
        let use_regs = if register_ops = [] then ""
                      else "    use xpr_all as " ^ (String.concat ", " register_ops) ^ ";\n" in
        let use_imms = String.concat "" (List.map (fun (name, typ) ->
          Printf.sprintf "    use %s as %s;\n" typ name
        ) immediate_ops) in
        
        (* Generate assembly syntax - use mnemonic with operands *)
        (* Reorder operands to match assembly syntax conventions *)
        let assembly_syntax = 
          let mnemonic_var = if enum_values <> [] then "opc" else "\"unknown\"" in
          let operand_str = 
            if constructor_name = "RTYPE" && List.length use_decls >= 3 then
              (* RTYPE: opc rd, rs1, rs2 (operands stored as rs2, rs1, rd) *)
              let rd = List.nth use_decls 2 in
              let rs1 = List.nth use_decls 1 in
              let rs2 = List.nth use_decls 0 in
              Printf.sprintf "%s \",\" %s \",\" %s" rd rs1 rs2
            else if constructor_name = "BTYPE" && List.length use_decls >= 3 then
              (* BTYPE: opc rs1, rs2, imm (operands stored as imm, rs2, rs1) *)
              let imm = List.nth use_decls 0 in
              let rs2 = List.nth use_decls 1 in
              let rs1 = List.nth use_decls 2 in
              Printf.sprintf "%s \",\" %s \",\" %s" rs1 rs2 imm
            else if constructor_name = "STORE" && List.length use_decls >= 3 then
              (* STORE: opc rs2, imm(rs1) (operands stored as imm, rs2, rs1) *)
              let imm = List.nth use_decls 0 in
              let rs2 = List.nth use_decls 1 in
              let rs1 = List.nth use_decls 2 in
              Printf.sprintf "%s \",\" %s \"(\" %s \")\"" rs2 imm rs1
            else if constructor_name = "LOAD" && List.length use_decls >= 3 then
              (* LOAD: opc rd, imm(rs1) (operands stored as imm, rs1, rd) *)
              let imm = List.nth use_decls 0 in
              let rs1 = List.nth use_decls 1 in
              let rd = List.nth use_decls 2 in
              Printf.sprintf "%s \",\" %s \"(\" %s \")\"" rd imm rs1
            else if constructor_name = "JALR" && List.length use_decls >= 3 then
              (* JALR: opc rd, imm(rs1) (operands stored as imm, rs1, rd) *)
              let imm = List.nth use_decls 0 in
              let rs1 = List.nth use_decls 1 in
              let rd = List.nth use_decls 2 in
              Printf.sprintf "%s \",\" %s \"(\" %s \")\"" rd imm rs1
            else
              String.concat " \",\" " use_decls
          in
          Printf.sprintf "    assembly { %s %s };" mnemonic_var operand_str
        in
        
        (* Helper: Find opcode pattern for a specific enum value *)
        let find_opcode_pattern enum_value_id =
          List.find_opt (fun opc ->
            Id.compare opc.oi_constructor clause.uc_constructor = 0 &&
            Id.compare opc.oi_enum_value enum_value_id = 0
          ) extracted_opcodes
        in
        
        (* Generate binary encoding based on instruction family *)
        let binary_encoding = 
          (* For RTYPE: FUNC7(opc) rs2 rs1 FUNC3(opc) rd OPCODE(opc) *)
          if constructor_name = "RTYPE" && List.length register_ops >= 3 then
            let rs2 = List.nth register_ops 0 in
            let rs1 = List.nth register_ops 1 in
            let rd = List.nth register_ops 2 in
            Printf.sprintf "    binary { FUNC7(opc) %s %s FUNC3(opc) %s OPCODE(opc) };" rs2 rs1 rd
          (* For ITYPE: imm rs1 FUNC3(opc) rd OPCODE(opc) *)
          else if constructor_name = "ITYPE" && List.length register_ops >= 2 && List.length immediate_ops >= 1 then
            let imm_name = fst (List.hd immediate_ops) in
            let rs1 = List.nth register_ops 0 in
            let rd = List.nth register_ops 1 in
            Printf.sprintf "    binary { %s %s FUNC3(opc) %s OPCODE(opc) };" imm_name rs1 rd
          (* For STORE: imm[11..5] rs2 rs1 FUNC3(opc) imm[4..0] OPCODE(opc) *)
          (* STORE has (imm, rs2, rs1) in operands *)
          else if constructor_name = "STORE" && List.length register_ops >= 2 && List.length immediate_ops >= 1 then
            let imm_name = fst (List.hd immediate_ops) in
            let rs2 = List.nth register_ops 0 in  (* First register is rs2 *)
            let rs1 = List.nth register_ops 1 in  (* Second register is rs1 *)
            Printf.sprintf "    binary { %s[11..5] %s %s FUNC3(opc) %s[4..0] OPCODE(opc) };" imm_name rs2 rs1 imm_name
          (* For BTYPE: imm[11] imm[9..4] rs2 rs1 FUNC3(opc) imm[3..0] imm[10] OPCODE(opc) *)
          (* BTYPE has (imm, rs2, rs1) in operands *)
          else if constructor_name = "BTYPE" && List.length register_ops >= 2 && List.length immediate_ops >= 1 then
            let imm_name = fst (List.hd immediate_ops) in
            let rs2 = List.nth register_ops 0 in  (* First register is rs2 *)
            let rs1 = List.nth register_ops 1 in  (* Second register is rs1 *)
            Printf.sprintf "    binary { %s[11..11] %s[9..4] %s %s FUNC3(opc) %s[3..0] %s[10..10] OPCODE(opc) };" 
              imm_name imm_name rs2 rs1 imm_name imm_name
          (* For UTYPE: imm rd OPCODE(opc) *)
          else if constructor_name = "UTYPE" && List.length register_ops >= 1 && List.length immediate_ops >= 1 then
            let imm_name = fst (List.hd immediate_ops) in
            let rd = List.nth register_ops 0 in
            Printf.sprintf "    binary { %s %s OPCODE(opc) };" imm_name rd
          (* For JTYPE: imm[19] imm[9..0] imm[10] imm[18..11] rd OPCODE(opc) *)
          else if constructor_name = "JAL" && List.length register_ops >= 1 && List.length immediate_ops >= 1 then
            let imm_name = fst (List.hd immediate_ops) in
            let rd = List.nth register_ops 0 in
            Printf.sprintf "    binary { %s[19..19] %s[9..0] %s[10..10] %s[18..11] %s OPCODE(opc) };" 
              imm_name imm_name imm_name imm_name rd
          (* For SHIFTIOP: FUNC7(opc) shamt rs1 FUNC3(opc) rd OPCODE(opc) *)
          else if constructor_name = "SHIFTIOP" && List.length register_ops >= 2 && List.length immediate_ops >= 1 then
            let shamt_name = fst (List.hd immediate_ops) in
            let rs1 = List.nth register_ops 0 in
            let rd = List.nth register_ops 1 in
            Printf.sprintf "    binary { FUNC7(opc) %s %s FUNC3(opc) %s OPCODE(opc) };" shamt_name rs1 rd
          (* Default: try to use extracted pattern or generate generic *)
          else
            (* Try to find a pattern from extracted opcodes *)
            match enum_values with
            | enum_value_id :: _ ->
                (match find_opcode_pattern enum_value_id with
                 | Some opc_info ->
                     if opc_info.oi_bit_pattern <> "TODO" then
                       Printf.sprintf "    binary { /* %s */ };" opc_info.oi_bit_pattern
                     else
                       Printf.sprintf "    binary { /* TODO: generate from encdec pattern for %s */ };" constructor_name
                 | None ->
                     Printf.sprintf "    binary { /* TODO: generate from encdec pattern for %s */ };" constructor_name)
            | [] ->
                Printf.sprintf "    binary { /* TODO: generate from encdec pattern for %s */ };" constructor_name
        in
        
        (* Generate semantics switch statement *)
        (* Replace src1/src2 with actual variable names based on instruction type *)
        let switch_cases = List.map (fun enum_value_id ->
          let op_name = string_of_id enum_value_id in
          let op_upper = String.uppercase_ascii op_name in
          let family_prefix = String.uppercase_ascii constructor_name in
          let operation = 
            if constructor_name = "RTYPE" && List.length register_ops >= 3 then
              (* Use actual variable names for RTYPE: rs1_val and rs2_val *)
              let rs1_var = (List.nth register_ops 1) ^ "_val" in
              let rs2_var = (List.nth register_ops 0) ^ "_val" in
              let op_str = generate_operation op_name in
              (* Replace src1 and src2 *)
              let op_str = 
                let len = String.length op_str in
                let buf = Buffer.create len in
                let rec replace i =
                  if i >= len then Buffer.contents buf
                  else if i + 4 <= len && String.sub op_str i 4 = "src1" then (
                    Buffer.add_string buf rs1_var;
                    replace (i + 4)
                  )
                  else if i + 4 <= len && String.sub op_str i 4 = "src2" then (
                    Buffer.add_string buf rs2_var;
                    replace (i + 4)
                  )
                  else (
                    Buffer.add_char buf op_str.[i];
                    replace (i + 1)
                  )
                in
                replace 0
              in
              op_str
            else if constructor_name = "BTYPE" && List.length register_ops >= 2 then
              (* Use actual variable names for BTYPE: rs1_val and rs2_val *)
              let rs1_var = (List.nth register_ops 1) ^ "_val" in
              let rs2_var = (List.nth register_ops 0) ^ "_val" in
              let op_str = generate_btype_condition op_name in
              (* Replace src1 and src2 *)
              let op_str = 
                let len = String.length op_str in
                let buf = Buffer.create len in
                let rec replace i =
                  if i >= len then Buffer.contents buf
                  else if i + 4 <= len && String.sub op_str i 4 = "src1" then (
                    Buffer.add_string buf rs1_var;
                    replace (i + 4)
                  )
                  else if i + 4 <= len && String.sub op_str i 4 = "src2" then (
                    Buffer.add_string buf rs2_var;
                    replace (i + 4)
                  )
                  else (
                    Buffer.add_char buf op_str.[i];
                    replace (i + 1)
                  )
                in
                replace 0
              in
              op_str
            else if constructor_name = "ITYPE" && List.length register_ops >= 1 && List.length immediate_ops >= 1 then
              (* Use actual variable names for ITYPE: rs1_val and immediate *)
              let rs1_var = (List.nth register_ops 0) ^ "_val" in
              let imm_name = fst (List.hd immediate_ops) in
              let op_str = generate_itype_operation op_name in
              (* Replace src1 and immediate *)
              let op_str = 
                let len = String.length op_str in
                let buf = Buffer.create len in
                let rec replace i =
                  if i >= len then Buffer.contents buf
                  else if i + 4 <= len && String.sub op_str i 4 = "src1" then (
                    Buffer.add_string buf rs1_var;
                    replace (i + 4)
                  )
                  else if i + 8 <= len && String.sub op_str i 8 = "immediate" then (
                    Buffer.add_string buf imm_name;
                    replace (i + 8)
                  )
                  else (
                    Buffer.add_char buf op_str.[i];
                    replace (i + 1)
                  )
                in
                replace 0
              in
              op_str
            else
              generate_operation op_name
          in
          Printf.sprintf "            case %s_%s:\n                result = %s;\n                break;" 
            family_prefix op_upper operation
        ) enum_values in
        
        let switch_body = String.concat "\n" switch_cases ^ 
          "\n            default:\n                result = 0;\n                break;" in
        
        (* Generate semantics section *)
        let semantics_vars = 
          if constructor_name = "BTYPE" then
            (* BTYPE: needs rs1, rs2, result, target_address *)
            if List.length register_ops >= 2 then
              let rs1 = List.nth register_ops 1 in
              let rs2 = List.nth register_ops 0 in
              Printf.sprintf "        uint32 %s_val, %s_val, result;" rs1 rs2
            else "        uint32 result;"
          else if constructor_name = "STORE" then
            (* STORE: needs address, data *)
            "        uint32 address, data;"
          else if constructor_name = "JAL" || constructor_name = "JALR" then
            (* JAL/JALR: needs target_address, current_pc *)
            "        uint32 target_address, current_pc;"
          else if register_ops <> [] then
            String.concat "\n        " (List.map (fun reg ->
              Printf.sprintf "uint32 %s_val;" reg
            ) register_ops) ^ "\n        uint32 result;"
          else "        uint32 result;"
        in
        
        let semantics_reads = 
          if constructor_name = "BTYPE" && List.length register_ops >= 2 then
            let rs1 = List.nth register_ops 1 in
            let rs2 = List.nth register_ops 0 in
            Printf.sprintf "        %s_val = rf_xpr_read(%s);\n        %s_val = rf_xpr_read(%s);" rs1 rs1 rs2 rs2
          else if constructor_name = "STORE" then
            "" (* Reads handled in writes section *)
          else
            String.concat "\n        " (List.map (fun reg ->
              Printf.sprintf "%s_val = rf_xpr_read(%s);" reg reg
            ) register_ops)
        in
        
        let semantics_writes = 
          if constructor_name = "BTYPE" then
            (* BTYPE: conditional branch - update PC if condition is true *)
            "        if (result) {\n            uint32 target_address = r_pc + (int32)imm - RISCV_INSTR_SIZE;\n            write_pc(target_address);\n        }"
          else if constructor_name = "STORE" then
            (* STORE: write to memory *)
            (match (register_ops, immediate_ops) with
             | (rs2 :: rs1 :: _, imm :: _) ->
                 Printf.sprintf "        uint32 address = rf_xpr_read(%s) + (int32)%s;\n        uint32 data = rf_xpr_read(%s);\n        store(opc, address, data);" 
                   rs1 (fst imm) rs2
             | _ -> "")
          else if constructor_name = "JAL" || constructor_name = "JALR" then
            (* JAL/JALR: write return address to rd, update PC *)
            (match register_ops with
             | rd :: _ ->
                 Printf.sprintf "        uint32 current_pc = read_pc();\n        rf_xpr_write(current_pc, %s);\n        uint32 target_address = current_pc + (int32)imm - RISCV_INSTR_SIZE;\n        write_pc(target_address);" rd
             | _ -> "")
          else if List.length register_ops > 0 then
            (* For RTYPE, rd is the 3rd register (index 2), for others it's typically the last *)
            let rd_idx = if constructor_name = "RTYPE" then 2 
                        else if constructor_name = "ITYPE" || constructor_name = "LOAD" then (List.length register_ops - 1)
                        else (List.length register_ops - 1) in
            if rd_idx < List.length register_ops then
              let rd = List.nth register_ops rd_idx in
              Printf.sprintf "        rf_xpr_write(result, %s);" rd
            else ""
          else ""
        in
        
        let semantics = 
          let reads_section = if semantics_reads <> "" then 
            "\n        // Read source operands\n" ^ semantics_reads ^ "\n"
          else "\n" in
          let writes_section = if semantics_writes <> "" then 
            "\n" ^ semantics_writes ^ "\n"
          else "\n" in
          Printf.sprintf "    semantics\n    {\n%s%s        switch (opc)\n        {\n%s\n        }%s    };" 
            semantics_vars reads_section switch_body writes_section
        in
        
        (* Generate opc set name *)
        let opc_set_name = "opc_" ^ constructor_lower in
        
        (* Put it all together *)
        Printf.sprintf "element i_%s\n{\n    use %s as opc;\n%s%s\n    %s\n\n    %s\n\n%s\n};"
          constructor_lower opc_set_name use_regs use_imms assembly_syntax binary_encoding semantics
    in
    
    (* Generate instruction elements for all families *)
    let generate_instruction_elements () =
      let elements = List.map generate_instruction_element ast_clauses in
      let non_empty = List.filter (fun s -> s <> "") elements in
      String.concat "\n\n" non_empty
    in
    
    (* Generate opcodes.hcodal file with enum definitions *)
    let generate_opcodes_header () =
      let header = 
        "/**\n" ^
        " * Generated opcodes header from Sail AST\n" ^
        " */\n\n" ^
        "#ifndef OPCODES_HCODAL_HG\n" ^
        "#define OPCODES_HCODAL_HG\n\n"
      in
      
      (* Group opcodes by constructor/family *)
      Printf.eprintf "=== Generating opcodes header from %d extracted opcodes ===\n" (List.length extracted_opcodes);
      let opcodes_by_family = 
        let family_map = List.fold_left (fun acc opc ->
          let family = string_of_id opc.oi_constructor in
          let existing = try List.assoc family acc with Not_found -> [] in
          (family, opc :: existing) :: (List.remove_assoc family acc)
        ) [] extracted_opcodes in
        family_map
      in
      
      (* Generate enum for each family *)
      let generate_enum_for_family (family_name, opcs) =
        if opcs = [] then ""
        else
          let family_upper = String.uppercase_ascii family_name in
          (* Determine enum type based on instruction family *)
          let (enum_type, _enum_width) = 
            match family_name with
            | "RTYPE" | "SHIFTIOP" -> ("uint17", 17)
            | "ITYPE" | "BTYPE" | "STORE" -> ("uint10", 10)
            | "UTYPE" | "JAL" -> ("uint7", 7)
            | _ -> ("uint10", 10)  (* Default *)
          in
          
          let enum_name = family_upper ^ "_OPCODES" in
          let enum_entries = List.map (fun opc ->
            let op_name = string_of_id opc.oi_enum_value in
            let op_upper = String.uppercase_ascii op_name in
            let enum_entry_name = family_upper ^ "_" ^ op_upper in
            (* Use computed value if available, otherwise use pattern *)
            let value = match opc.oi_computed_value with
              | Some v -> v
              | None -> 
                  (match opc.oi_opcode with
                   | Some opc_val -> opc_val
                   | None -> "0b0")
            in
            Printf.sprintf "    %s = %s" enum_entry_name value
          ) opcs in
          
          Printf.sprintf "// %s Opcodes\n" family_name ^
          Printf.sprintf "enum %s : %s {\n" enum_name enum_type ^
          String.concat ",\n" enum_entries ^
          "\n};\n"
      in
      
      let enums = List.map generate_enum_for_family opcodes_by_family in
      let non_empty_enums = List.filter (fun s -> s <> "") enums in
      
      header ^
      String.concat "\n" non_empty_enums ^
      "\n#endif\n"
    in
    
    (* Generate ops file content - basic helpers + relative addresses *)
    let ops_file_content = 
      "/* Generated Codal ISA Ops from Sail AST */\n\n" ^
      "/*\n" ^
      " * Creating definitions to parse out the individual instructions bits to their appropriate fields:\n" ^
      " *      func7\n" ^
      " *      func3\n" ^
      " *      opcode\n" ^
      " */\n\n" ^
      "#define FUNC7(opc)     opc[16..10]\n" ^
      "#define FUNC3(opc)     opc[9..7]\n" ^
      "#define OPCODE(opc)     opc[6..0]\n\n" ^
      "//  Opcode macro element\n" ^
      "#define DEF_OPC(name, syntax, opc) \\\n" ^
      "    element opc_##name \\\n" ^
      "    { \\\n" ^
      "        assembly {syntax}; \\\n" ^
      "        binary {opc}; \\\n" ^
      "        return {opc}; \\\n" ^
      "    };\n\n" ^
      generate_register_definitions () ^ "\n\n" ^
      "// Instructions that support an immediate operand, require the definitaion of immediate elements\n\n" ^
      (String.concat "\n\n" (generate_immediate_definitions ())) ^ "\n\n" ^
      "///////////////////////////////////////////////////////////////////////////////\n" ^
      "//                     relative address operands\n" ^
      "/////////////////////////////////////////////////////////////////////////////\n\n" ^
      (String.concat "\n\n" (generate_address_operands ())) ^ "\n"
    in
    
    (* Generate instruction elements from CDEF *)
    let codal_definitions = List.map codal_cdef cdefs in
    
    (* Generate ISA set from all instruction families *)
    let generate_isa_set () =
      let element_names = List.filter_map (fun clause ->
        let constructor_name = string_of_id clause.uc_constructor in
        let enum_values = match extract_enum_type_from_clause clause with
          | Some enum_id ->
              (match IdMap.find_opt enum_id enum_info with
               | Some ids -> if ids <> [] then Some ids else None
               | None -> None)
          | None -> None
        in
        match enum_values with
        | Some _ -> Some ("i_" ^ String.lowercase_ascii constructor_name)
        | None -> None
      ) ast_clauses in
      if element_names = [] then "set isa = i_rtype_alu;"
      else "set isa = " ^ (String.concat ", " element_names) ^ ";"
    in
    
    (* Main codal file content - includes ops file, DEF_OPC calls, and instructions *)
    let main_file_content =
      "/* Generated Codal ISA from Sail AST */\n\n" ^
      "#include \"opcodes.hcodal\"\n" ^
      "#include \"utils.hcodal\"\n" ^
      "#include \"config.hcodal\"\n" ^
      "#include \"debug.hcodal\"\n" ^
      "#include \"isa_ops.codal\"\n\n" ^
      "/* Main ISA set */\n" ^
      generate_isa_set () ^ "\n\n" ^
      "/* Start section */\n" ^
      "start\n{\n  roots = { isa };\n};\n\n" ^
      "/* RISC-V opcode definitions from enum types */\n" ^
      generate_def_opc_calls () ^ "\n\n" ^
      generate_opc_set () ^ "\n\n" ^
      "/* Instruction elements generated from Sail union clauses */\n" ^
      generate_instruction_elements () ^ "\n\n" ^
      "/* Additional definitions from JIB */\n" ^
      (String.concat "\n\n" codal_definitions)
    in
    
    (* Generate opcodes header *)
    let opcodes_header_content = generate_opcodes_header () in
    
    (* Return tuple (ops_content, main_content, opcodes_header_content) *)
    (ops_file_content, main_file_content, opcodes_header_content)




  (* Helper function to check if string starts with prefix *)
  let string_starts_with str prefix =
    let len = String.length prefix in
    String.length str >= len && String.sub str 0 len = prefix

  (* Helper function to check if a location is from the target Sail file *)
  (* Default to riscv_insts_base.sail, but can be configured *)
  let target_sail_file = ref "riscv_insts_base.sail"
  
  let is_from_main_sail_file loc =
    match Reporting.simp_loc loc with
    | Some (pos1, _pos2) ->
        let filename = pos1.Lexing.pos_fname in
        let basename = Filename.basename filename in
        (* Check if the file matches the target file *)
        basename = !target_sail_file
    | None -> false
  
  (* Filter function to keep only definitions from the target Sail file (not included files) *)
  let filter_isa_definitions cdefs =
    let is_from_main_file_cdef = function
      | CDEF_aux (_, def_annot) -> is_from_main_sail_file def_annot.loc
    in
    
    let is_essential_type = function
      | CDEF_aux (CDEF_type (CTD_enum (id, _)), _) ->
          (* Keep essential enums used in instructions: rop, iop, bop, sop, uop *)
          let enum_name = string_of_id id in
          enum_name = "rop" || enum_name = "iop" || enum_name = "bop" || 
          enum_name = "sop" || enum_name = "uop" || enum_name = "ropw" || 
          enum_name = "sopw"
      | CDEF_aux (CDEF_type (CTD_variant (id, _, _)), _) ->
          (* Keep essential variants like ast *)
          string_of_id id = "ast"
      | _ -> false
    in
    
    let filtered = List.filter (fun cdef -> 
      is_from_main_file_cdef cdef || is_essential_type cdef
    ) cdefs in
    
    (* Debug: print what we're keeping *)
    Printf.eprintf "Filtering: keeping %d out of %d definitions\n" (List.length filtered) (List.length cdefs);
    List.iter (fun cdef ->
      match cdef with
      | CDEF_aux (CDEF_fundef (id, _, _, _), def_annot) -> 
          Printf.eprintf "Keeping function: %s from %s\n" (string_of_id id) 
            (match Reporting.simp_loc def_annot.loc with
             | Some (pos, _) -> Filename.basename pos.Lexing.pos_fname
             | None -> "unknown")
      | CDEF_aux (CDEF_val (id, _, _, _, _), def_annot) -> 
          Printf.eprintf "Keeping value: %s from %s\n" (string_of_id id)
            (match Reporting.simp_loc def_annot.loc with
             | Some (pos, _) -> Filename.basename pos.Lexing.pos_fname
             | None -> "unknown")
      | CDEF_aux (CDEF_type (CTD_enum (id, _)), def_annot) -> 
          Printf.eprintf "Keeping enum: %s from %s\n" (string_of_id id)
            (match Reporting.simp_loc def_annot.loc with
             | Some (pos, _) -> Filename.basename pos.Lexing.pos_fname
             | None -> "unknown")
      | CDEF_aux (CDEF_type (CTD_variant (id, _, _)), def_annot) -> 
          Printf.eprintf "Keeping variant: %s from %s\n" (string_of_id id)
            (match Reporting.simp_loc def_annot.loc with
             | Some (pos, _) -> Filename.basename pos.Lexing.pos_fname
             | None -> "unknown")
      | _ -> ()
    ) filtered;
    
    filtered

  let compile_ast env effects basename ast _sail_source =
    (* Convert Sail AST to JIB intermediate representation 
    gets env and effects to create ctx and use ast&ctx to compile ast to jib
  with instantiated jib compiler
    *)
    let union_info = collect_union_clauses ast.defs in
    let enum_info = collect_enum_literals ast.defs in
    let mapping_info = collect_mappings ast.defs in
    let cdefs, _ = jib_of_ast env effects ast in
    
    (* Filter to keep only definitions from the main Sail file (not included files) *)
    let filtered_cdefs = filter_isa_definitions cdefs in
    
    (* Generate the actual Codal translation for .codal file using FILTERED definitions *)
    let cdef_aux_list = List.map (fun cdef -> match cdef with | CDEF_aux (cdef_aux, _) -> cdef_aux) filtered_cdefs in
    (*So anonymous function which is used to strip the CDEF_aux from the cdef is applied to the filtered_cdefs list
    and the result is stored in cdef_aux_list list*)
    
    let (ops_content, main_content, opcodes_header_content) = jib_to_codal union_info enum_info mapping_info cdef_aux_list in
    
    (* Determine output directory: try codal_plugin relative to current directory *)
    (* This assumes we're running from sail-riscv/model and want files in codal_plugin/ *)
    let output_dir = 
      let try_paths = ["../../codal_plugin"; "../codal_plugin"; "codal_plugin"] in
      let rec find_dir = function
        | [] -> ""  (* Fallback to current directory *)
        | path :: rest ->
            (try
              if Sys.file_exists path && Sys.is_directory path then
                path ^ "/"
              else
                find_dir rest
            with
            | _ -> find_dir rest)
      in
      find_dir try_paths
    in
    
    (* Write the ops file (isa_ops.codal) *)
    let ops_filename = output_dir ^ "isa_ops.codal" in
    let ops_out = open_out ops_filename in
    output_string ops_out ops_content;
    flush ops_out;
    close_out ops_out;
    Printf.eprintf "Generated ops file: %s\n" ops_filename;
    
    (* Write the opcodes header file (opcodes.hcodal) *)
    let opcodes_filename = output_dir ^ "opcodes.hcodal" in
    let opcodes_out = open_out opcodes_filename in
    output_string opcodes_out opcodes_header_content;
    flush opcodes_out;
    close_out opcodes_out;
    Printf.eprintf "Generated opcodes header file: %s\n" opcodes_filename;
    
    (* Prepare header and body for main file *)
    let header =
      if Config.generate_header then
        Some (String.concat "\n"
                (["#pragma once";
                  "/* Generated Codal ISA from Sail AST */";
                  Printf.sprintf "/* module: %s */" basename] @
                 List.map (fun inc -> Printf.sprintf "#include \"%s\"" inc) Config.header_includes))
      else None
    in
    let body = main_content in
    
    (* Return header and main body (main file will be written by plugin) *)
    (header, body)
end

