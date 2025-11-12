(****************************************************************************)
(* JIB Output Backend                                                      *)
(* Converts Sail AST to JIB and outputs the JIB representation            *)
(****************************************************************************)

open Libsail

open Ast
open Ast_util (*string_of_id comes from here*)
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


  (* Instruction type classification *)
  type instruction_type = 
    | RType of name * name * name  (* rd, rs1, rs2 *)
    | IType of name * name * name  (* rd, rs1, imm *)
    | BType of name * name * name  (* rs1, rs2, imm *)
    | JType of name * name         (* rd, imm *)
    | UType of name * name         (* rd, imm *)
    | LoadType of name * name * name (* rd, rs1, imm *)
    | StoreType of name * name * name (* rs1, rs2, imm *)
    | Other

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

  

  (* Classify instruction based on name and arguments *)
  let classify_instruction func_name args =
    let name_lower = String.lowercase_ascii func_name in
    match (name_lower, List.length args) with
    | (name, 3) when string_contains name "add" || string_contains name "sub" || 
                     string_contains name "and" || string_contains name "or" || 
                     string_contains name "xor" || string_contains name "sll" || 
                     string_contains name "srl" || string_contains name "sra" ||
                     string_contains name "slt" -> 
        RType (List.nth args 0, List.nth args 1, List.nth args 2)
    | (name, 3) when string_contains name "addi" || string_contains name "andi" || 
                     string_contains name "ori" || string_contains name "xori" ||
                     string_contains name "slti" -> 
        IType (List.nth args 0, List.nth args 1, List.nth args 2)
    | (name, 3) when string_contains name "beq" || string_contains name "bne" || 
                     string_contains name "blt" || string_contains name "bge" ||
                     string_contains name "bltu" || string_contains name "bgeu" -> 
        BType (List.nth args 0, List.nth args 1, List.nth args 2)
    | (name, 3) when string_contains name "lw" || string_contains name "lh" || 
                     string_contains name "lb" || string_contains name "lhu" ||
                     string_contains name "lbu" -> 
        LoadType (List.nth args 0, List.nth args 1, List.nth args 2)
    | (name, 3) when string_contains name "sw" || string_contains name "sh" || 
                     string_contains name "sb" -> 
        StoreType (List.nth args 0, List.nth args 1, List.nth args 2)
    | (name, 2) when string_contains name "jal" -> 
        JType (List.nth args 0, List.nth args 1)
    | (name, 2) when string_contains name "lui" || string_contains name "auipc" -> 
        UType (List.nth args 0, List.nth args 1)
    | _ -> Other

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

 (*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)   
  (* Generate binary encoding for instructions *)
  let generate_binary_encoding _func_name args =  (*Function ignores functioon name *)
    match List.length args with
    | 3 -> "FUNC7_OPC rs2 rs1 FUNC3_OPC rd OPCODE_OPC"
    | 2 -> "imm rs1 FUNC3_OPC rd OPCODE_OPC"
    | 1 -> "imm rd OPCODE_OPC"
    | _ -> "OPCODE_OPC"

(*i_stype_store missing*)
(*eventually we will print binary{above return}*)
(*Only looks at number of arguments, which might be wrong*)
(*3->RTYPE->i_rtype_alu, JALR,BTYPE, ITYPE*)
(*2->UTYPE->*,i_type_alu,i_type_loads*)
(*1->JAL->*)

  (* Generate semantics for instructions *)
  let generate_semantics func_name _args _instrs =
    Printf.sprintf "// %s semantics\n    // TODO: Implement specific semantics" func_name

  (* Generate opcode definitions *)
  let generate_opcode_definitions cdefs =
    let opcodes = List.fold_left (fun acc cdef ->
      match cdef with
      | CDEF_fundef (id, _, _, _) ->
          let func_name = string_of_id id in
          let opcode_name = String.uppercase_ascii func_name in
          Printf.sprintf "#define %s_OPCODE 0x%02x" opcode_name (Hashtbl.hash func_name mod 256) :: acc
      | _ -> acc
    ) [] cdefs in
    String.concat "\n" (List.rev opcodes)

  (* Generate function field definitions, Are we using this? *)
  let generate_function_fields cdefs =
    let fields = List.fold_left (fun acc cdef ->
      match cdef with
      | CDEF_fundef (id, _, _, _) ->
          let func_name = string_of_id id in
          let opcode_name = String.uppercase_ascii func_name in
          Printf.sprintf "#define FUNC7_%s 0x%02x" opcode_name (Hashtbl.hash (func_name ^ "_func7") mod 256) ::
          Printf.sprintf "#define FUNC3_%s 0x%02x" opcode_name (Hashtbl.hash (func_name ^ "_func3") mod 256) ::
          acc
      | _ -> acc
    ) [] cdefs in
    String.concat "\n" (List.rev fields)

  (* This generates i_rtype_alu falan herhalde*)
  let generate_instruction_sets cdefs =
    let sets = List.fold_left (fun acc cdef -> (*i_*)
      match cdef with
      | CDEF_fundef (id, _, _, _) ->
          let func_name = string_of_id id in
          Printf.sprintf "i_%s" func_name :: acc
      | _ -> acc
    ) [] cdefs in
    let sets_str = String.concat ",\n    " (List.rev sets) in
    Printf.sprintf "set isa = %s;" sets_str




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

  (* Handle Sail register definitions and convert to Codal format *)
  let handle_register_definitions cdefs =
    let register_defs = List.filter_map (fun cdef ->
      match cdef with
      | CDEF_register (id, ctyp, instrs) ->
          let reg_name = string_of_name id in
          let reg_type = string_of_ctyp ctyp in
          Some (reg_name, reg_type, instrs)
      | _ -> None
    ) cdefs in
    
    if register_defs = [] then ""
    else
      let register_elements = List.map (fun (reg_name, reg_type, _instrs) ->
        match reg_name with
        | "x0" -> 
            "element x_0\n{\n    assembly{STRINGIZE(x0)};\n    binary  {0:bit[5]};\n    return{0};\n};\n\nelement x_0_alias : assembler_alias(x_0)\n{\n    assembly { \"zero\" };\n    binary { 0:bit[5] };\n};"
        | name when String.length name >= 2 && String.sub name 0 1 = "x" ->
            let reg_num = try int_of_string (String.sub name 1 (String.length name - 1)) with _ -> 0 in
            let aliases = match reg_num with
              | 1 -> "ra" | 2 -> "sp" | 3 -> "gp" | 4 -> "tp" | 5 -> "t0" | 6 -> "t1" | 7 -> "t2"
              | 8 -> "fp" | 9 -> "s1" | 10 -> "a0" | 11 -> "a1" | 12 -> "a2" | 13 -> "a3" | 14 -> "a4" | 15 -> "a5"
              | 16 -> "a6" | 17 -> "a7" | 18 -> "s2" | 19 -> "s3" | 20 -> "s4" | 21 -> "s5" | 22 -> "s6" | 23 -> "s7"
              | 24 -> "s8" | 25 -> "s9" | 26 -> "s10" | 27 -> "s11" | 28 -> "t3" | 29 -> "t4" | 30 -> "t5" | 31 -> "t6"
              | _ -> "x" ^ string_of_int reg_num
            in
            Printf.sprintf "DEF_REG_ALIAS(%d, \"%s\")       // %s" reg_num aliases name
        | _ -> Printf.sprintf "// Register: %s : %s" reg_name reg_type
      ) register_defs in
      
      let register_sets = [
        "set xpr_general : register_class(rf_xpr);";
        "set xpr_all;";
        "set xpr_all += xpr_general, x_0, x_0_alias;";
      ] in
      
      String.concat "\n" (register_elements @ [""] @ register_sets)

  (* Handle Sail mapping definitions and convert to Codal format *)
  let handle_mapping_definitions cdefs =
    let mapping_defs = List.filter_map (fun cdef ->
      match cdef with
      | CDEF_val (id, _, _, _, _) ->
          let val_name = string_of_id id in
          if String.contains val_name 'r' && String.contains val_name 'g' then
            Some val_name
          else None
      | _ -> None
    ) cdefs in
    
    if mapping_defs = [] then ""
    else
      let mapping_comments = List.map (fun name ->
        Printf.sprintf "// Mapping: %s -> converted to Codal element definitions" name
      ) mapping_defs in
      String.concat "\n" (["// Sail mappings converted to Codal elements:"] @ mapping_comments)

  (* it takes argument in type cdef_aux list and returns a tuple of strings *)
  let jib_to_codal (cdefs : cdef_aux list) =
    (* Extract enum values from rop type for generating opcodes *)
    let rop_values =
      List.find_map (fun cdef ->
        match cdef with
        | CDEF_type (CTD_enum (id, ids)) when string_of_id id = "rop" ->
            Some (List.map string_of_id ids)
        | _ -> None
      ) cdefs
      |> Option.value ~default:[]
    in

    (***************************************************************************************************************)
    let codal_cdef = function
      | CDEF_fundef (id, _return_id_opt, args, instrs) ->
          let func_name = string_of_id id in
          
          (* Special handling for execute function - generate i_rtype_alu with switch *)
          let result = if func_name = "execute" && rop_values <> [] then begin
            (* Build switch cases directly from rop enum values *)
            let switch_cases = List.map (fun op_name ->
              let op_upper = String.uppercase_ascii op_name in
              let operation = generate_operation op_name in
              Printf.sprintf "            case RTYPE_%s:\n                %s\n                break;" 
                op_upper operation
            ) rop_values in
            
            let switch_body = String.concat "\n" switch_cases ^ 
              "\n            default:\n                result = 0;\n                break;" in
            
            Printf.sprintf "element i_rtype_alu\n{\n    use opc_rtype_alu as opc;\n    use xpr_all as rs1, rs2, rd;\n\n    assembly { opc rd \",\" rs1 \",\" rs2};\n    binary { FUNC7(opc) rs2 rs1 FUNC3(opc) rd OPCODE(opc) };\n\n    semantics\n    {\n        uint32 src1, src2, result;\n\n        src1 = rf_xpr_read(rs1);\n        src2 = rf_xpr_read(rs2);\n\n        switch (opc)\n        {\n%s\n        }\n\n        rf_xpr_write(result, rd);\n    };\n};" switch_body
          end else begin
            let instr_type = classify_instruction func_name args in
            
            (* Generate Codal instruction element following RISC-V pattern *)
            match instr_type with
          | RType (rd, rs1, rs2) ->
              Printf.sprintf "element i_%s\n{\n  use xpr_all as %s, %s, %s;\n  \n  assembly { \"%s\" %s, %s, %s };\n  \n  binary { FUNC7_%s %s %s FUNC3_%s %s OPCODE_%s };\n  \n  semantics\n  {\n    uint32 src1, src2, result;\n    \n    src1 = rf_xpr_read(%s);\n    src2 = rf_xpr_read(%s);\n    \n    result = %s;\n    \n    rf_xpr_write(result, %s);\n  };\n};" 
                func_name
                (string_of_name rs1) (string_of_name rs2) (string_of_name rd)
                func_name (string_of_name rd) (string_of_name rs1) (string_of_name rs2)
                (String.uppercase_ascii func_name) (string_of_name rs2) (string_of_name rs1) (String.uppercase_ascii func_name) (string_of_name rd) (String.uppercase_ascii func_name)
                (string_of_name rs1) (string_of_name rs2)
                (generate_operation func_name)
                (string_of_name rd)
                
          | IType (rd, rs1, imm) ->
              Printf.sprintf "element i_%s\n{\n  use xpr_all as %s, %s;\n  use simm12 as %s;\n  \n  assembly { \"%s\" %s, %s, %s };\n  \n  binary { %s %s FUNC3_%s %s OPCODE_%s };\n  \n  semantics\n  {\n    uint32 src1, result;\n    int32 immediate;\n    \n    src1 = rf_xpr_read(%s);\n    immediate = (int32) %s;\n    \n    result = %s;\n    \n    rf_xpr_write(result, %s);\n  };\n};" 
                func_name
                (string_of_name rs1) (string_of_name rd) (string_of_name imm)
                func_name (string_of_name rd) (string_of_name rs1) (string_of_name imm)
                (string_of_name imm) (string_of_name rs1) (String.uppercase_ascii func_name) (string_of_name rd) (String.uppercase_ascii func_name)
                (string_of_name rs1) (string_of_name imm)
                (generate_itype_operation func_name)
                (string_of_name rd)
                
          | BType (rs1, rs2, imm) ->
              Printf.sprintf "element i_%s\n{\n  use xpr_all as %s, %s;\n  use relative_addr12 as %s;\n  \n  assembly { \"%s\" %s, %s, %s };\n  \n  binary { %s[11..11] %s[9..4] %s %s FUNC3_%s %s[3..0] %s[10..10] OPCODE_%s };\n  \n  semantics\n  {\n    uint32 src1, src2, target_address;\n    uint32 result;\n    \n    src1 = rf_xpr_read(%s);\n    src2 = rf_xpr_read(%s);\n    \n    result = %s;\n    \n    if (result) {\n      target_address = r_pc + (int32)%s - RISCV_INSTR_SIZE;\n      write_pc(target_address);\n    }\n  };\n};" 
                func_name
                (string_of_name rs1) (string_of_name rs2) (string_of_name imm)
                func_name (string_of_name rs1) (string_of_name rs2) (string_of_name imm)
                (string_of_name imm) (string_of_name imm) (string_of_name rs2) (string_of_name rs1) (String.uppercase_ascii func_name) (string_of_name imm) (string_of_name imm) (String.uppercase_ascii func_name)
                (string_of_name rs1) (string_of_name rs2)
                (generate_btype_condition func_name)
                (string_of_name imm)
                
          | JType (rd, imm) ->
              Printf.sprintf "element i_%s\n{\n  use xpr_all as %s;\n  use relative_addr20 as %s;\n  \n  assembly { \"%s\" %s, %s };\n  \n  binary { %s[19..19] %s[9..0] %s[10..10] %s[18..11] %s OPCODE_%s };\n  \n  semantics\n  {\n    uint32 target_address, current_pc;\n    \n    current_pc = read_pc();\n    rf_xpr_write(current_pc, %s);\n    target_address = current_pc + %s - RISCV_INSTR_SIZE;\n    write_pc(target_address);\n  };\n};" 
                func_name
                (string_of_name rd) (string_of_name imm)
                func_name (string_of_name rd) (string_of_name imm)
                (string_of_name imm) (string_of_name imm) (string_of_name imm) (string_of_name imm) (string_of_name rd) (String.uppercase_ascii func_name)
                (string_of_name rd) (string_of_name imm)
                
          | UType (rd, imm) ->
              Printf.sprintf "element i_%s\n{\n  use xpr_all as %s;\n  use uimm20 as %s;\n  \n  assembly { \"%s\" %s, %s };\n  \n  binary { %s %s OPCODE_%s };\n  \n  semantics\n  {\n    uint32 result;\n    \n    result = %s;\n    \n    rf_xpr_write(result, %s);\n  };\n};" 
                func_name
                (string_of_name rd) (string_of_name imm)
                func_name (string_of_name rd) (string_of_name imm)
                (string_of_name imm) (string_of_name rd) (String.uppercase_ascii func_name)
                (generate_utype_operation func_name)
                (string_of_name rd)
                
          | LoadType (rd, rs1, imm) ->
              Printf.sprintf "element i_%s\n{\n  use xpr_all as %s, %s;\n  use simm12 as %s;\n  \n  assembly { \"%s\" %s, %s(%s) };\n  \n  binary { %s %s FUNC3_%s %s OPCODE_%s };\n  \n  semantics\n  {\n    uint32 address, result;\n    \n    address = rf_xpr_read(%s) + (int32) %s;\n    result = load(opc, address);\n    rf_xpr_write(result, %s);\n  };\n};" 
                func_name
                (string_of_name rs1) (string_of_name rd) (string_of_name imm)
                func_name (string_of_name rd) (string_of_name imm) (string_of_name rs1)
                (string_of_name imm) (string_of_name rs1) (String.uppercase_ascii func_name) (string_of_name rd) (String.uppercase_ascii func_name)
                (string_of_name rs1) (string_of_name imm)
                (string_of_name rd)
                
          | StoreType (rs1, rs2, imm) ->
              Printf.sprintf "element i_%s\n{\n  use xpr_all as %s, %s;\n  use simm12 as %s;\n  \n  assembly { \"%s\" %s, %s(%s) };\n  \n  binary { %s[11..5] %s %s FUNC3_%s %s[4..0] OPCODE_%s };\n  \n  semantics\n  {\n    uint32 address, data;\n    \n    address = rf_xpr_read(%s) + (int32) %s;\n    data = rf_xpr_read(%s);\n    store(opc, address, data);\n  };\n};" 
                func_name
                (string_of_name rs1) (string_of_name rs2) (string_of_name imm)
                func_name (string_of_name rs2) (string_of_name imm) (string_of_name rs1)
                (string_of_name imm) (string_of_name rs2) (string_of_name rs1) (String.uppercase_ascii func_name) (string_of_name imm) (String.uppercase_ascii func_name)
                (string_of_name rs1) (string_of_name imm) (string_of_name rs2)
                
          | Other ->
              (* Fallback for other instruction types *)
          let args_str = String.concat ", " (List.map string_of_name args) in
              Printf.sprintf "element %s\n{\n  use xpr_all as %s;\n  \n  assembly { \"%s\" %s };\n  \n  binary { %s };\n  \n  semantics\n  {\n    %s\n  };\n};" 
                func_name
                (String.concat ", " (List.map string_of_name args))
                func_name
                args_str
                (generate_binary_encoding func_name args)
                (generate_semantics func_name args instrs)
          end
          in
          result
            
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
    (* Generate DEF_OPC definitions from rop enum values *)
    let generate_def_opc_calls () =
      if rop_values = [] then ""
      else
        let opc_defs = List.map (fun op_name ->
          let op_lower = String.lowercase_ascii op_name in
          Printf.sprintf "DEF_OPC(%s, \"%s\", RTYPE_%s)" op_lower op_lower (String.uppercase_ascii op_name)
        ) rop_values in
        String.concat "\n" opc_defs
    in
    
    (* Generate opcode set from rop enum values *)
    let generate_opc_set () =
      if rop_values = [] then ""
      else
        let opc_names = List.map (fun op -> "opc_" ^ String.lowercase_ascii op) rop_values in
        Printf.sprintf "set opc_rtype_alu = %s;" (String.concat ", " opc_names)
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
    
    (* Main codal file content - includes ops file, DEF_OPC calls, and instructions *)
    let main_file_content =
      "/* Generated Codal ISA from Sail AST */\n\n" ^
      "#include \"opcodes.hcodal\"\n" ^
      "#include \"utils.hcodal\"\n" ^
      "#include \"config.hcodal\"\n" ^
      "#include \"debug.hcodal\"\n" ^
      "#include \"isa_ops.codal\"\n\n" ^
      "/* Main ISA set */\n" ^
      "set isa = i_rtype_alu;\n\n" ^
      "/* Start section */\n" ^
      "start\n{\n  roots = { isa };\n};\n\n" ^
      "/* RISC-V opcode definitions from rop enum */\n" ^
      generate_def_opc_calls () ^ "\n\n" ^
      generate_opc_set () ^ "\n\n" ^
      (String.concat "\n\n" codal_definitions)
    in
    
    (* Return tuple (ops_content, main_content) *)
    (ops_file_content, main_file_content)


  (* Generate binary encoding following RISC-V pattern, Are we using this? *)
  let generate_binary_encoding func_name args =
    match List.length args with
    | 0 -> "OPCODE_" ^ (String.uppercase_ascii func_name)
    | 1 -> "imm @ encdec_reg(" ^ (List.hd args |> string_of_name) ^ ") @ OPCODE_" ^ (String.uppercase_ascii func_name)
    | 2 -> "imm @ encdec_reg(" ^ (List.nth args 0 |> string_of_name) ^ ") @ encdec_reg(" ^ (List.nth args 1 |> string_of_name) ^ ") @ OPCODE_" ^ (String.uppercase_ascii func_name)
    | 3 -> "encdec_reg(" ^ (List.nth args 0 |> string_of_name) ^ ") @ encdec_reg(" ^ (List.nth args 1 |> string_of_name) ^ ") @ encdec_reg(" ^ (List.nth args 2 |> string_of_name) ^ ") @ OPCODE_" ^ (String.uppercase_ascii func_name)
    | _ -> "/* Complex encoding */"

  (* Generate semantics following RISC-V pattern,Are we using this? *)
  let generate_semantics _func_name args instrs =
    let arg_vars = List.mapi (fun i arg -> 
      Printf.sprintf "    uint32 src%d = rf_xpr_read(%s);" (i+1) (string_of_name arg)
    ) args in
    
    let operations = List.map (fun instr ->
      match instr with
      | I_aux (I_copy (clexp, cval), _) ->
          let lval_str = match clexp with
            | CL_id (id, _) -> string_of_name id
            | _ -> "result"
          in
          let exp_str = match cval with
            | V_call (op, _args) when string_of_op op = "add" ->
                "src1 + src2"
            | V_call (op, _args) when string_of_op op = "sub" ->
                "src1 - src2"
            | V_call (op, _args) when string_of_op op = "and" ->
                "src1 & src2"
            | V_call (op, _args) when string_of_op op = "or" ->
                "src1 | src2"
            | V_call (op, _args) when string_of_op op = "xor" ->
                "src1 ^ src2"
            | _ -> "/* Operation */"
          in
          Printf.sprintf "    %s = %s;" lval_str exp_str
      | _ -> "    /* Instruction */"
    ) instrs in
    
    let write_result = match args with
      | [] -> ""
      | _ -> "    rf_xpr_write(result, " ^ (List.hd args |> string_of_name) ^ ");"
    in
    
    String.concat "\n" (arg_vars @ operations @ [write_result])


  (* Helper function to check if string starts with prefix *)
  let string_starts_with str prefix =
    let len = String.length prefix in
    String.length str >= len && String.sub str 0 len = prefix

  (* Helper function to check if a location is from mvp_addition.sail *)
  let is_from_main_sail_file loc =
    match Reporting.simp_loc loc with
    | Some (pos1, _pos2) ->
        let filename = pos1.Lexing.pos_fname in
        let basename = Filename.basename filename in
        (* Check if the file is mvp_addition.sail, not riscv_types_minimal.sail or other included files *)
        basename = "mvp_addition.sail"
    | None -> false
  
  (* Filter function to keep only definitions from mvp_addition.sail (not included files) *)
  let filter_isa_definitions cdefs =
    let is_from_main_file_cdef = function
      | CDEF_aux (_, def_annot) -> is_from_main_sail_file def_annot.loc
    in
    
    let is_essential_type = function
      | CDEF_aux (CDEF_type (CTD_enum (id, _)), _) ->
          (* Keep essential enums like rop *)
          string_of_id id = "rop"
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
    let cdefs, _ = jib_of_ast env effects ast in
    
    (* Filter to keep only definitions from the main Sail file (not included files) *)
    let filtered_cdefs = filter_isa_definitions cdefs in
    
    (* Generate the actual Codal translation for .codal file using FILTERED definitions *)
    let cdef_aux_list = List.map (fun cdef -> match cdef with | CDEF_aux (cdef_aux, _) -> cdef_aux) filtered_cdefs in
    (*So anonymous function which is used to strip the CDEF_aux from the cdef is applied to the filtered_cdefs list
    and the result is stored in cdef_aux_list list*)
    
    let (ops_content, main_content) = jib_to_codal cdef_aux_list in
    
    (* Write the ops file (isa_ops.codal) *)
    let ops_filename = "isa_ops.codal" in
    let ops_out = open_out ops_filename in
    output_string ops_out ops_content;
    flush ops_out;
    close_out ops_out;
    Printf.eprintf "Generated ops file: %s\n" ops_filename;
    
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

