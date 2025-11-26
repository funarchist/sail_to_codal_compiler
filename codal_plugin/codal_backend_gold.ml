(****************************************************************************)
(* CodAL Backend - Direct Sail AST to CodAL Translation                     *)
(*                                                                          *)
(* This backend translates Sail RISC-V instruction descriptions to CodAL   *)
(* WITHOUT using JIB intermediate representation.                           *)
(*                                                                          *)
(* Key features:                                                             *)
(* 1. Extract encdec mappings BEFORE rewrites -> opcode bit patterns        *)
(* 2. Extract execute function clauses -> semantic translation              *)
(* 3. Direct AST-to-CodAL translation for semantics                         *)
(****************************************************************************)

open Libsail

open Ast
open Ast_util (*string_of_id comes from here*)
open Ast_defs
open Type_check

(* NOTE: We intentionally do NOT use Jib, Jib_compile, Jib_util
   We work directly with the Sail AST for both opcode extraction
   AND semantic translation. *)

(* Simplified configuration - no JIB options needed *)
module type CODALGEN_CONFIG = sig
  val generate_header : bool
  val header_includes : string list
end

(* NOTE: C_config module removed - we don't use JIB *)

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
  
  (****************************************************************************)
  (* SAIL EXPRESSION TO CODAL TRANSLATOR                                      *)
  (*                                                                          *)
  (* Translates Sail AST expressions directly to CodAL semantic code.         *)
  (* This replaces the old heuristic-based approach with real AST translation *)
  (****************************************************************************)

  (* Helper function to check if string contains substring *)
  let string_contains str substr =
    try
      let len = String.length substr in
      let rec check i =
        if i + len > String.length str then false
        else if String.sub str i len = substr then true
        else check (i + 1)
      in
      check 0
    with _ -> false

  (* Translate Sail expression to CodAL expression string *)
  (* This is the core of semantic translation *)
  let rec translate_exp (exp : 'a exp) (var_map : (string * string) list) : string =
    let E_aux (exp_aux, _) = exp in
    match exp_aux with
    (* Identifiers - look up in variable mapping *)
    | E_id id ->
        let name = string_of_id id in
        (match List.assoc_opt name var_map with
         | Some mapped -> mapped
         | None -> name)
    
    (* Function application - translate common Sail functions to CodAL *)
    | E_app (func_id, args) ->
        let func_name = string_of_id func_id in
        (match func_name with
         (* Register read: X(rs1), rX_bits(rs1) -> rf_xpr_read(rs1) *)
         | "X" | "rX_bits" ->
             (match args with
              | [arg] -> Printf.sprintf "rf_xpr_read(%s)" (translate_exp arg var_map)
              | _ -> Printf.sprintf "rf_xpr_read(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         
         (* Arithmetic operations - translate to CodAL operators *)
         | "add_bits" | "add_vec" | "add_atom" ->
             (match args with
              | [a; b] -> Printf.sprintf "(%s + %s)" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> Printf.sprintf "add(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         | "sub_vec" | "sub_bits" | "sub_atom" ->
             (match args with
              | [a; b] -> Printf.sprintf "(%s - %s)" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> Printf.sprintf "sub(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         
         (* Bitwise operations - translate to CodAL operators *)
         | "xor_vec" | "xor_bits" ->
             (match args with
              | [a; b] -> Printf.sprintf "(%s ^ %s)" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> Printf.sprintf "xor(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         | "and_vec" | "and_bits" ->
             (match args with
              | [a; b] -> Printf.sprintf "(%s & %s)" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> Printf.sprintf "and(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         | "or_vec" | "or_bits" ->
             (match args with
              | [a; b] -> Printf.sprintf "(%s | %s)" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> Printf.sprintf "or(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         
         (* Shift operations - translate to CodAL operators *)
         | "shift_bits_left" | "shiftl" ->
             (match args with
              | [a; b] -> Printf.sprintf "(%s << %s)" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> Printf.sprintf "shiftl(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         | "shift_bits_right" | "shiftr" ->
             (match args with
              | [a; b] -> Printf.sprintf "(%s >> %s)" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> Printf.sprintf "shiftr(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         | "shift_bits_right_arith" | "arith_shiftr" ->
             (match args with
              | [src; amt] -> Printf.sprintf "((int32)%s >> %s)" (translate_exp src var_map) (translate_exp amt var_map)
              | _ -> "0")
         
         (* Bit extraction - subrange_bits(vec, hi, lo) -> vec[hi..lo] *)
         | "subrange_bits" | "vector_subrange" ->
             (match args with
              | [vec; hi; lo] -> 
                  Printf.sprintf "%s[%s..%s]" (translate_exp vec var_map) (translate_exp hi var_map) (translate_exp lo var_map)
              | _ -> Printf.sprintf "subrange(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         
         (* Sign/zero extension *)
         | "sign_extend" ->
             (match args with
              | [_size; arg] -> Printf.sprintf "(int32)%s" (translate_exp arg var_map)
              | [arg] -> Printf.sprintf "(int32)%s" (translate_exp arg var_map)
              | _ -> Printf.sprintf "sign_extend(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         | "zero_extend" ->
             (match args with
              | [_size; arg] -> Printf.sprintf "(uint32)%s" (translate_exp arg var_map)
              | [arg] -> Printf.sprintf "(uint32)%s" (translate_exp arg var_map)
              | _ -> Printf.sprintf "zero_extend(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         
         (* Bool to bits *)
         | "bool_to_bits" ->
             (match args with
              | [arg] -> Printf.sprintf "((%s) ? 1 : 0)" (translate_exp arg var_map)
              | _ -> "0")
         
         (* Comparison operators wrapped in functions *)
         | "operator <_s" | "lt_int" ->
             (match args with
              | [a; b] -> Printf.sprintf "((int32)%s < (int32)%s)" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> "0")
         | "operator <_u" | "lt_bits" ->
             (match args with
              | [a; b] -> Printf.sprintf "((uint32)%s < (uint32)%s)" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> "0")
         | "operator >=_s" | "gteq_int" ->
             (match args with
              | [a; b] -> Printf.sprintf "((int32)%s >= (int32)%s)" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> "0")
         | "operator >=_u" | "gteq_bits" ->
             (match args with
              | [a; b] -> Printf.sprintf "((uint32)%s >= (uint32)%s)" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> "0")
         | "eq_bits" | "eq_int" ->
             (match args with
              | [a; b] -> Printf.sprintf "(%s == %s)" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> "0")
         | "neq_bits" | "neq_int" ->
             (match args with
              | [a; b] -> Printf.sprintf "(%s != %s)" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> "0")
         
         (* Get arch PC / next PC *)
         | "get_arch_pc" | "PC" -> "r_pc - RISCV_INSTR_SIZE"
         | "get_next_pc" -> "r_pc"
         
         (* Ignore type annotation functions *)
         | "mult_atom" | "pow2" | "log2_xlen" -> 
             (match args with
              | [] -> func_name
              | [arg] -> translate_exp arg var_map
              | _ -> translate_exp (List.hd (List.rev args)) var_map)
         
         (* Default: preserve function call but still translate args *)
         | _ -> Printf.sprintf "%s(%s)" func_name (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
    
    (* Binary operations *)
    | E_app_infix (left, op_id, right) ->
        let op_name = string_of_id op_id in
        let left_str = translate_exp left var_map in
        let right_str = translate_exp right var_map in
        let op_str = match op_name with
          | "+" -> "+"
          | "-" -> "-"
          | "&" -> "&"
          | "|" -> "|"
          | "^" -> "^"
          | "<<" -> "<<"
          | ">>" -> ">>"
          | "==" -> "=="
          | "!=" -> "!="
          | "<_s" -> "<"  (* signed less than *)
          | ">=_s" -> ">="  (* signed greater or equal *)
          | "<_u" -> "<"  (* unsigned - cast needed *)
          | ">=_u" -> ">="  (* unsigned *)
          | _ -> op_name
        in
        (* Handle signed/unsigned comparisons *)
        if op_name = "<_s" || op_name = ">=_s" then
          Printf.sprintf "((int32)%s %s (int32)%s)" left_str op_str right_str
        else if op_name = "<_u" || op_name = ">=_u" then
          Printf.sprintf "((uint32)%s %s (uint32)%s)" left_str op_str right_str
        else
          Printf.sprintf "(%s %s %s)" left_str op_str right_str
    
    (* Literal values *)
    | E_lit lit ->
        (match lit with
         | L_aux (L_num n, _) -> Big_int.to_string n
         | L_aux (L_hex h, _) -> "0x" ^ h
         | L_aux (L_bin b, _) -> "0b" ^ b
         | L_aux (L_true, _) -> "1"
         | L_aux (L_false, _) -> "0"
         | L_aux (L_unit, _) -> ""
         | _ -> "/* literal */")
    
    (* Vector/bitvector access: x[n..m] -> extract bits *)
    | E_vector_access (vec, idx) ->
        Printf.sprintf "%s[%s]" (translate_exp vec var_map) (translate_exp idx var_map)
    
    | E_vector_subrange (vec, hi, lo) ->
        Printf.sprintf "%s[%s..%s]" (translate_exp vec var_map) 
          (translate_exp hi var_map) (translate_exp lo var_map)
    
    (* Concatenation *)
    | E_vector_append (left, right) ->
        Printf.sprintf "(%s @ %s)" (translate_exp left var_map) (translate_exp right var_map)
    
    (* Block - translate last expression *)
    | E_block exps ->
        (match List.rev exps with
         | [] -> ""
         | last :: _ -> translate_exp last var_map)
    
    (* Let binding *)
    | E_let (LB_aux (LB_val (_pat, bind_exp), _), body) ->
        let _bind_str = translate_exp bind_exp var_map in
        (* For now, just translate body - proper let handling would update var_map *)
        translate_exp body var_map
    
    (* Match expression - used for switch cases *)
    | E_match (scrutinee, _cases) ->
        let scrut_str = translate_exp scrutinee var_map in
        Printf.sprintf "/* match %s { ... } */" scrut_str
    
    (* If-then-else *)
    | E_if (cond, then_exp, else_exp) ->
        let cond_str = translate_exp cond var_map in
        let then_str = translate_exp then_exp var_map in
        let else_str = translate_exp else_exp var_map in
        Printf.sprintf "(%s) ? (%s) : (%s)" cond_str then_str else_str
    
    (* Tuple *)
    | E_tuple exps ->
        Printf.sprintf "(%s)" (String.concat ", " (List.map (fun e -> translate_exp e var_map) exps))
    
    (* Cast *)
    | E_typ (typ, exp) ->
        let exp_str = translate_exp exp var_map in
        (* Simple type cast translation *)
        let Typ_aux (typ_aux, _) = typ in
        (match typ_aux with
         | Typ_id id when string_of_id id = "xlenbits" -> Printf.sprintf "(uint32)%s" exp_str
         | _ -> exp_str)
    
    (* Default: show AST for debugging *)
    | _ -> "/* TODO: translate expression */"

  (* Collect execute function clauses from AST *)
  (* Returns list of (func_id, pexp) where pexp is the full pattern expression *)
  let collect_execute_clauses defs =
    let rec find_clauses acc = function
      | [] -> acc
      | DEF_aux (DEF_fundef (FD_aux (FD_function (_, _, funcls), _)), _) :: rest ->
          let execute_clauses = List.filter_map (fun fcl ->
            match fcl with
            | FCL_aux (FCL_funcl (func_id, pexp), _) ->
                if string_of_id func_id = "execute" then
                  Some (func_id, pexp)  (* Keep the full Pat_aux wrapper *)
                else None
          ) funcls in
          find_clauses (acc @ execute_clauses) rest
      | DEF_aux (DEF_scattered (SD_aux (SD_funcl (FCL_aux (FCL_funcl (func_id, pexp), _)), _)), _) :: rest ->
          if string_of_id func_id = "execute" then
            find_clauses ((func_id, pexp) :: acc) rest  (* Keep the full Pat_aux wrapper *)
          else
            find_clauses acc rest
      | _ :: rest -> find_clauses acc rest
    in
    find_clauses [] defs

  (* Parse execute clause to extract constructor, args, and body *)
  (* Input: Pat_aux (pexp_aux, annot) *)
  let parse_execute_clause pexp =
    let Pat_aux (pexp_aux, _) = pexp in
    match pexp_aux with
    | Pat_exp (P_aux (P_app (constructor_id, arg_pats), _), body) ->
        (* Extract argument names from patterns *)
        let arg_ids = List.filter_map (fun pat ->
          match pat with
          | P_aux (P_id id, _) -> Some id
          | P_aux (P_typ (_, P_aux (P_id id, _)), _) -> Some id
          | _ -> None
        ) arg_pats in
        Some (constructor_id, arg_ids, body)
    | Pat_when (P_aux (P_app (constructor_id, arg_pats), _), _guard, body) ->
        let arg_ids = List.filter_map (fun pat ->
          match pat with
          | P_aux (P_id id, _) -> Some id
          | P_aux (P_typ (_, P_aux (P_id id, _)), _) -> Some id
          | _ -> None
        ) arg_pats in
        Some (constructor_id, arg_ids, body)
    | _ -> None

  (* Debug: Print expression structure *)
  (* Extract the expression for a specific enum case from a match expression *)
  (* Searches recursively through the AST to find match expressions *)
  let rec find_match_arm_for_enum (exp : 'a exp) (enum_value_id : id) (var_map : (string * string) list) : string option =
    let E_aux (exp_aux, _) = exp in
    match exp_aux with
    (* Block: search through all expressions *)
    | E_block exps ->
        let rec search = function
          | [] -> None
          | e :: rest ->
              (match find_match_arm_for_enum e enum_value_id var_map with
               | Some result -> Some result
               | None -> search rest)
        in
        search exps
    
    (* Assignment: X(rd) = match op { ... } - check RHS *)
    | E_assign (_, rexp) ->
        find_match_arm_for_enum rexp enum_value_id var_map
    
    (* Let binding: check body *)
    | E_let (_, body) ->
        find_match_arm_for_enum body enum_value_id var_map
    
    (* Function application: X(rd) = match op {...} is actually E_app(wX_bits, ...) *)
    (* In Sail, register writes like X(rd) = value are represented as wX_bits(rd, value) *)
    | E_app (_func_id, args) ->
        (* Search through all arguments for a match expression *)
        let rec search_args = function
          | [] -> None
          | arg :: rest ->
              (match find_match_arm_for_enum arg enum_value_id var_map with
               | Some result -> Some result
               | None -> search_args rest)
        in
        search_args args
    
    (* Match expression: this is what we're looking for! *)
    | E_match (_scrutinee, cases) ->
        (* Search through match arms for the enum value *)
        let find_arm = function
          | Pat_aux (Pat_exp (P_aux (P_id case_id, _), arm_exp), _) ->
              if Id.compare case_id enum_value_id = 0 then
                Some (translate_exp arm_exp var_map)
              else None
          | Pat_aux (Pat_exp (P_aux (P_app (case_id, _), _), arm_exp), _) ->
              if Id.compare case_id enum_value_id = 0 then
                Some (translate_exp arm_exp var_map)
              else None
          | Pat_aux (Pat_when (P_aux (P_id case_id, _), _, arm_exp), _) ->
              if Id.compare case_id enum_value_id = 0 then
                Some (translate_exp arm_exp var_map)
              else None
          | _ -> None
        in
        List.find_map find_arm cases
    
    (* If expression: search both branches *)
    | E_if (_, then_exp, else_exp) ->
        (match find_match_arm_for_enum then_exp enum_value_id var_map with
         | Some result -> Some result
         | None -> find_match_arm_for_enum else_exp enum_value_id var_map)
    
    | _ -> None

  (* Translate execute clause body for a specific enum case *)
  (* Returns CodAL semantic expression for that case *)
  (* execute_clauses: list of (func_id, pexp_funcl) where pexp_funcl is Pat_aux(...) *)
  let translate_execute_for_case constructor_name (enum_value_id : id) 
      execute_clauses 
      (operand_names : string list) : string =
    (* Find the execute clause for this constructor *)
    let matching_clause = List.find_opt (fun (_func_id, pexp) ->
      match parse_execute_clause pexp with
      | Some (constr_id, _, _) -> string_of_id constr_id = constructor_name
      | None -> false
    ) execute_clauses in
    
    match matching_clause with
    | Some (_, pexp) ->
        (match parse_execute_clause pexp with
         | Some (_constr_id, arg_ids, body) ->
             (* Build variable mapping from Sail args to CodAL operands *)
             (* For RTYPE: args are [rs2, rs1, rd, op] *)
             (* Map them to operand_names which should be [rs2, rs1, rd] *)
             let var_map = List.filter_map (fun (i, arg_id) ->
               let sail_name = string_of_id arg_id in
               (* Skip the "op" parameter - it's the enum discriminator *)
               if sail_name = "op" then None
               else
                 let codal_name = 
                   if i < List.length operand_names then
                     List.nth operand_names i
                   else sail_name
                 in
                 Some (sail_name, codal_name)
             ) (List.mapi (fun i a -> (i, a)) arg_ids) in
             
             (* Search for the match expression and extract the arm for this enum *)
             (match find_match_arm_for_enum body enum_value_id var_map with
              | Some arm_translation -> arm_translation
              | None -> 
                  (* Fallback: translate whole body *)
                  translate_exp body var_map)
         | None -> "/* could not parse execute clause */")
    | None -> 
        (* No execute clause found - generate placeholder *)
        Printf.sprintf "/* TODO: translate execute for %s.%s */" 
          constructor_name (string_of_id enum_value_id)






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

  (****************************************************************************)
  (* AST to CodAL Translation                                                 *)
  (*                                                                          *)
  (* Main translation function - takes extracted AST info and generates:     *)
  (* - opcodes.hcodal: enum definitions with bit patterns from encdec        *)
  (* - isa_ops.codal: register/immediate definitions                         *)
  (* - main .codal: instruction elements with semantics from execute         *)
  (****************************************************************************)
  let ast_to_codal union_info enum_info (mapping_info : 'a mapping_collection) defs =
    (* Collect execute function clauses for semantic translation *)
    let execute_clauses = collect_execute_clauses defs in
    
    (* Find and parse encdec mapping to extract opcode patterns *)
    let encdec_id = mk_id "encdec" in
    let encdec_mapping = IdMap.find_opt encdec_id mapping_info in
    
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
    (* NOTE: Currently unused but kept for potential future use *)
    let _extract_bit_pattern_from_mpexp (mpexp : 'b mpexp) : string option =
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
    
    (* Helper: Extract binary literal value from mpat *)
    let extract_bin_literal_from_mpat (mpat : 'b mpat) : (string * int) option =
      match mpat with
      | MP_aux (MP_lit (L_aux (L_bin bits, _)), _) ->
          (try Some (bits, int_of_string ("0b" ^ bits)) with _ -> None)
      | MP_aux (MP_lit (L_aux (L_hex hex, _)), _) ->
          (try Some (hex, int_of_string ("0x" ^ hex)) with _ -> None)
      | _ -> None
    in
    
    (* Helper: Extract pattern parts from concatenation and compute opcode *)
    (* Returns: (all_parts_list, (func7, func3, opcode)) *)
    (* Now handles MP_vector_concat which is the actual AST structure *)
    let extract_pattern_parts_from_concat (mpexp : 'b mpexp) : (string list * (int option * int option * int option)) =
      match mpexp with
      | MPat_aux (MPat_pat (MP_aux (MP_vector_concat pats, _)), _) ->
          (* MP_vector_concat contains a list of mpat elements *)
          (* For RTYPE: [func7, rs2, rs1, func3, rd, opcode] *)
          let all_parts = List.filter_map (fun mpat ->
            match extract_bin_literal_from_mpat mpat with
            | Some (bits, _) -> Some ("0b" ^ bits)
            | None ->
                (* Check if it's a function application like encdec_reg *)
                (match mpat with
                 | MP_aux (MP_app (id, _), _) -> Some ("<" ^ string_of_id id ^ ">")
                 | MP_aux (MP_id id, _) -> Some (string_of_id id)
                 | _ -> None)
          ) pats in
          
          (* Extract all binary literals with their positions *)
          let indexed_literals = List.filter_map (fun (i, mpat) ->
            match extract_bin_literal_from_mpat mpat with
            | Some (bits, value) -> Some (i, bits, value)
            | None -> None
          ) (List.mapi (fun i p -> (i, p)) pats) in
          
          (* For RTYPE: first 7-bit is func7, 3-bit is func3, last 7-bit is opcode *)
          (* The order in pats is: [0]=func7, [1]=rs2, [2]=rs1, [3]=func3, [4]=rd, [5]=opcode *)
          let func7_opt = 
            (* First 7-bit literal (index 0) *)
            match List.find_opt (fun (i, bits, _) -> i = 0 && String.length bits = 7) indexed_literals with
            | Some (_, _, value) -> Some value
            | None -> None
          in
          let func3_opt =
            (* 3-bit literal *)
            match List.find_opt (fun (_, bits, _) -> String.length bits = 3) indexed_literals with
            | Some (_, _, value) -> Some value
            | None -> None
          in
          let opcode_opt =
            (* Last 7-bit literal (highest index among 7-bit literals) *)
            let seven_bit_lits = List.filter (fun (_, bits, _) -> String.length bits = 7) indexed_literals in
            match List.sort (fun (i1, _, _) (i2, _, _) -> compare i2 i1) seven_bit_lits with
            | (_, _, value) :: _ -> Some value
            | [] -> None
          in
          
          (all_parts, (func7_opt, func3_opt, opcode_opt))
      
      | MPat_aux (MPat_pat mpat, _) ->
          (* Single pattern - extract if it's a literal *)
          (match extract_bin_literal_from_mpat mpat with
           | Some (bits, value) ->
               let len = String.length bits in
               let func7_opt = if len = 7 then Some value else None in
               let func3_opt = if len = 3 then Some value else None in
               let opcode_opt = if len = 7 then Some value else None in
               (["0b" ^ bits], (func7_opt, func3_opt, opcode_opt))
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
    (* NOTE: Currently unused but kept for potential single-value lookups *)
    let _resolve_helper_mapping (helper_name : string) (enum_value_id : id) : int option =
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
    
    (* Helper: Get all entries from a helper mapping (e.g., encdec_iop, encdec_bop) *)
    (* Returns list of (enum_id, bit_value) *)
    let get_helper_mapping_entries (helper_name : string) : (id * int) list =
      let helper_id = mk_id helper_name in
      match IdMap.find_opt helper_id mapping_info with
      | Some info ->
          List.filter_map (fun mapcl ->
            match mapcl with
            | MCL_aux (MCL_bidir (left_mpexp, right_mpexp), _) ->
                (* Left: enum value, Right: bit pattern *)
                let enum_opt = match left_mpexp with
                  | MPat_aux (MPat_pat (MP_aux (MP_id id, _)), _) -> Some id
                  | _ -> None
                in
                let value_opt = match extract_bit_literal right_mpexp with
                  | Some (_, v) -> Some v
                  | None -> None
                in
                (match (enum_opt, value_opt) with
                 | (Some e, Some v) -> Some (e, v)
                 | _ -> None)
            | _ -> None
          ) info.mi_clauses
      | None -> []
    in
    
    (* Check if an identifier is a variable (not an enum literal) *)
    let is_variable_not_enum (id : id) : bool =
      let name = string_of_id id in
      (* Common variable names used in encdec patterns *)
      name = "op" || name = "rd" || name = "rs1" || name = "rs2" || 
      name = "imm" || name = "shamt" || name = "pred" || name = "succ" ||
      name = "width" || name = "is_unsigned"
    in
    
    (* Parse encdec mapping clauses to extract opcode information *)
    (* Returns a LIST of opcode_info because one clause might expand to multiple opcodes *)
    let parse_encdec_clause (mapcl : 'b mapcl) : opcode_info list =
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
               let constructor_name = string_of_id constructor_id in
               let _enum_name = string_of_id enum_value_id in
               
               (* Extract pattern parts and compute opcode value *)
               let (pattern_parts, (func7_opt, func3_opt, opcode_opt)) = 
                 extract_pattern_parts_from_concat right_mpexp in
               
               (* Check if enum_value_id is a variable (like "op") rather than literal (like "ADD") *)
               if is_variable_not_enum enum_value_id then begin
                 (* This is a parametric encoding - expand using helper mapping *)
                 let helper_name = match constructor_name with
                   | "ITYPE" -> "encdec_iop"
                   | "BTYPE" -> "encdec_bop"
                   | "UTYPE" -> "encdec_uop"
                   | "SHIFTIOP" -> "encdec_sop"
                   | _ -> ""
                 in
                 if helper_name <> "" then begin
                   let entries = get_helper_mapping_entries helper_name in
                   (* Generate one opcode_info for each entry in the helper mapping *)
                   List.map (fun (entry_enum_id, entry_value) ->
                     let bit_pattern = String.concat " " pattern_parts in
                     (* For UTYPE: entry_value is 7-bit opcode *)
                     (* For ITYPE/BTYPE: entry_value is 3-bit func3, combine with base opcode *)
                     let (resolved_func3, resolved_opcode, computed) = 
                       match constructor_name with
                       | "UTYPE" ->
                           (* UTYPE: opcode only (7 bits) *)
                           (None, Some entry_value, Some (int_to_binary_string entry_value 7))
                       | "ITYPE" | "BTYPE" | "STORE" ->
                           (* func3 @ opcode (10 bits) *)
                           let base_opc = match opcode_opt with Some v -> v | None -> 0 in
                           let full = (entry_value lsl 7) lor base_opc in
                           (Some entry_value, opcode_opt, Some (int_to_binary_string full 10))
                       | "SHIFTIOP" ->
                           (* func7 @ func3 @ opcode (17 bits) *)
                           let base_opc = match opcode_opt with Some v -> v | None -> 0 in
                           let f7 = match func7_opt with Some v -> v | None -> 0 in
                           let full = (f7 lsl 10) lor (entry_value lsl 7) lor base_opc in
                           (Some entry_value, opcode_opt, Some (int_to_binary_string full 17))
                       | _ ->
                           (Some entry_value, opcode_opt, None)
                     in
                     { oi_constructor = constructor_id;
                       oi_enum_value = entry_enum_id;
                       oi_bit_pattern = bit_pattern;
                       oi_func7 = (match func7_opt with Some v -> Some (int_to_binary_string v 7) | None -> None);
                       oi_func3 = (match resolved_func3 with Some v -> Some (int_to_binary_string v 3) | None -> None);
                       oi_opcode = (match resolved_opcode with Some v -> Some (int_to_binary_string v 7) | None -> None);
                       oi_computed_value = computed }
                   ) entries
                 end else
                   (* No helper mapping found - return single entry *)
                   let bit_pattern = if pattern_parts = [] then "TODO" else String.concat " " pattern_parts in
                   [{ oi_constructor = constructor_id;
                      oi_enum_value = enum_value_id;
                      oi_bit_pattern = bit_pattern;
                      oi_func7 = None; oi_func3 = None; oi_opcode = opcode_opt |> Option.map (fun v -> int_to_binary_string v 7);
                      oi_computed_value = None }]
               end else begin
                 (* This is a direct encoding (like RTYPE with specific enum value) *)
                 let bit_pattern = if pattern_parts = [] then "TODO" 
                                  else String.concat " " pattern_parts in
                 let computed_value = compute_opcode_value (func7_opt, func3_opt, opcode_opt) constructor_name in
                 
                 (* Extract func7, func3, opcode as strings *)
                 let func7_str = match func7_opt with
                   | Some v -> Some (int_to_binary_string v 7)
                   | None -> None
                 in
                 let func3_str = match func3_opt with
                   | Some v -> Some (int_to_binary_string v 3)
                   | None -> None
                 in
                 let opcode_str = match opcode_opt with
                   | Some v -> Some (int_to_binary_string v 7)
                   | None -> None
                 in
                 
                 [{ oi_constructor = constructor_id; 
                    oi_enum_value = enum_value_id; 
                    oi_bit_pattern = bit_pattern;
                    oi_func7 = func7_str;
                    oi_func3 = func3_str;
                    oi_opcode = opcode_str;
                    oi_computed_value = computed_value }]
               end
           | None -> [])
      | _ -> []
    in
    
    (* Extract all opcodes from encdec mapping *)
    let extracted_opcodes = match encdec_mapping with
      | Some info ->
          List.concat_map parse_encdec_clause info.mi_clauses
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

    (* NOTE: codal_cdef removed - we don't use JIB, all generation from AST *)
    

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
        
        (* Determine source registers (not destination) for local variable generation *)
        (* rd is destination, rs1/rs2 are sources *)
        let (source_regs, dest_reg) = 
          let num_regs = List.length register_ops in
          if constructor_name = "RTYPE" && num_regs >= 3 then
            (* RTYPE: rs2, rs1, rd -> sources are rs2, rs1 *)
            ([List.nth register_ops 0; List.nth register_ops 1], Some (List.nth register_ops 2))
          else if (constructor_name = "ITYPE" || constructor_name = "SHIFTIOP" || constructor_name = "LOAD" || constructor_name = "JALR") && num_regs >= 2 then
            (* ITYPE: rs1, rd -> source is rs1 *)
            ([List.nth register_ops 0], Some (List.nth register_ops 1))
          else if (constructor_name = "BTYPE" || constructor_name = "STORE") && num_regs >= 2 then
            (* BTYPE/STORE: rs2, rs1 -> both are sources, no dest *)
            ([List.nth register_ops 0; List.nth register_ops 1], None)
          else if (constructor_name = "UTYPE" || constructor_name = "JAL") && num_regs >= 1 then
            (* UTYPE/JAL: rd -> no sources, rd is dest *)
            ([], Some (List.nth register_ops 0))
          else
            (register_ops, None)
        in
        
        (* Create local variable names: src1, src2 for source registers *)
        let src_var_names = List.mapi (fun i _ -> Printf.sprintf "src%d" (i + 1)) source_regs in
        let src_var_map = List.combine source_regs src_var_names in
        
        (* Build var_map for translate_execute_for_case that maps reg names to src vars *)
        let operand_to_src_map = List.map (fun (reg, src) -> (reg, src)) src_var_map in
        
        (* Generate switch cases using LOCAL VARIABLES *)
        let switch_cases = List.map (fun enum_value_id ->
          let op_name = string_of_id enum_value_id in
          let op_upper = String.uppercase_ascii op_name in
          let family_prefix = String.uppercase_ascii constructor_name in
          
          (* Translate execute clause, mapping register reads to local vars *)
          let operand_names = List.map fst operands in
          let operation = translate_execute_for_case constructor_name enum_value_id 
                           execute_clauses operand_names in
          
          (* Replace rf_xpr_read(regname) with local variable name *)
          let operation_with_locals = List.fold_left (fun acc (reg, src) ->
            (* Replace rf_xpr_read(reg) with src *)
            let pattern = Printf.sprintf "rf_xpr_read(%s)" reg in
            let rec replace_all s =
              try
                let idx = Str.search_forward (Str.regexp_string pattern) s 0 in
                let before = String.sub s 0 idx in
                let after = String.sub s (idx + String.length pattern) (String.length s - idx - String.length pattern) in
                replace_all (before ^ src ^ after)
              with Not_found -> s
            in
            replace_all acc
          ) operation operand_to_src_map in
          
          Printf.sprintf "            case %s_%s:\n                result = %s;\n                break;" 
            family_prefix op_upper operation_with_locals
        ) enum_values in
        
        let switch_body = String.concat "\n" switch_cases ^ 
          "\n            default:\n                result = 0;\n                break;" in
        
        (* Generate semantics section with local variables *)
        (* Declare local vars for sources + result (+ immediate if needed) *)
        let semantics_vars = 
          if constructor_name = "BTYPE" then
            "        uint32 result, target_address;\n        uint32 " ^ (String.concat ", " src_var_names) ^ ";"
          else if constructor_name = "STORE" then
            "        uint32 address, data;"
          else if constructor_name = "JAL" || constructor_name = "JALR" then
            "        uint32 target_address, current_pc;"
          else if source_regs <> [] then
            "        uint32 " ^ (String.concat ", " src_var_names) ^ ", result;"
          else 
            "        uint32 result;"
        in
        
        (* Generate reads into LOCAL VARIABLES (only source registers, not dest) *)
        let semantics_reads = 
          if constructor_name = "STORE" then
            "" (* Reads handled in writes section *)
          else if source_regs <> [] then
            String.concat "\n        " (List.map2 (fun reg src ->
              Printf.sprintf "%s = rf_xpr_read(%s);" src reg
            ) source_regs src_var_names)
          else ""
        in
        
        let semantics_writes = 
          if constructor_name = "BTYPE" then
            "        if (result) write_pc(target_address);"
          else if constructor_name = "STORE" then
            (match (register_ops, immediate_ops) with
             | (rs2 :: rs1 :: _, imm :: _) ->
                 Printf.sprintf "        address = rf_xpr_read(%s) + (int32)%s;\n        data = rf_xpr_read(%s);\n        store(opc, address, data);" 
                   rs1 (fst imm) rs2
             | _ -> "")
          else if constructor_name = "JAL" || constructor_name = "JALR" then
            (match dest_reg with
             | Some rd ->
                 Printf.sprintf "        current_pc = read_pc();\n        rf_xpr_write(current_pc, %s);\n        target_address = current_pc + (int32)imm - RISCV_INSTR_SIZE;\n        write_pc(target_address);" rd
             | None -> "")
          else 
            (match dest_reg with
             | Some rd -> Printf.sprintf "        rf_xpr_write(result, %s);" rd
             | None -> "")
        in
        
        (* Add immediate variable declaration and read if needed *)
        let (semantics_vars, semantics_reads) = 
          if immediate_ops <> [] && constructor_name <> "STORE" && constructor_name <> "JAL" && constructor_name <> "JALR" then
            let imm_name = fst (List.hd immediate_ops) in
            let imm_type = snd (List.hd immediate_ops) in
            let cast_type = if String.sub imm_type 0 1 = "s" then "int32" else "uint32" in
            (semantics_vars ^ "\n        " ^ cast_type ^ " immediate;",
             semantics_reads ^ (if semantics_reads <> "" then "\n        " else "") ^ 
               Printf.sprintf "immediate = (%s) %s;" cast_type imm_name)
          else (semantics_vars, semantics_reads)
        in
        
        (* Add target_address computation for BTYPE *)
        let semantics_reads = 
          if constructor_name = "BTYPE" then
            semantics_reads ^ "\n\n        target_address = r_pc + (int32)imm - RISCV_INSTR_SIZE;"
          else semantics_reads
        in
        
        let semantics = 
          let reads_section = if semantics_reads <> "" then 
            "\n\n        // read source operands\n        " ^ semantics_reads ^ "\n"
          else "\n" in
          let writes_section = if semantics_writes <> "" then 
            "\n\n        // store result\n" ^ semantics_writes ^ "\n"
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
    
    (* NOTE: codal_definitions removed - all generated from AST *)
    
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
    
    (* Generate per-family block: DEF_OPC, set, element together *)
    let generate_family_block (clause : union_clause_info) : string =
      let constructor_name = string_of_id clause.uc_constructor in
      let constructor_lower = String.lowercase_ascii constructor_name in
      
      (* Get enum values for this family *)
      let enum_values = match extract_enum_type_from_clause clause with
        | Some enum_id -> (match IdMap.find_opt enum_id enum_info with
            | Some ids -> ids | None -> [])
        | None -> []
      in
      
      if enum_values = [] then "" else
        let family_prefix = String.uppercase_ascii constructor_name in
        
        (* Generate DEF_OPC calls for this family *)
        let opc_defs = String.concat "\n" (List.map (fun enum_value_id ->
          let op_name = string_of_id enum_value_id in
          let op_lower = String.lowercase_ascii op_name in
          let mnemonic = match find_mnemonic_for_enum constructor_name enum_value_id with
            | Some m -> m | None -> op_lower in
          Printf.sprintf "DEF_OPC(%s, \"%s\", %s_%s)" 
            op_lower mnemonic family_prefix (String.uppercase_ascii op_name)
        ) enum_values) in
        
        (* Generate set for this family *)
        let opc_names = List.map (fun id -> "opc_" ^ String.lowercase_ascii (string_of_id id)) enum_values in
        let opc_set = Printf.sprintf "set opc_%s = %s;" constructor_lower (String.concat ", " opc_names) in
        
        (* Generate element for this family *)
        let element = generate_instruction_element clause in
        
        (* Combine: comment, DEF_OPC, set, element *)
        Printf.sprintf "// %s Instructions\n\n%s\n\n%s\n\n%s" 
          constructor_name opc_defs opc_set element
    in
    
    (* Generate all family blocks *)
    let generate_all_family_blocks () =
      let blocks = List.filter_map (fun clause ->
        let block = generate_family_block clause in
        if block = "" then None else Some block
      ) ast_clauses in
      String.concat "\n\n" blocks
    in
    
    (* Main codal file content - grouped per family like isa.codal *)
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
      generate_all_family_blocks ()
    in
    
    (* Generate opcodes header *)
    let opcodes_header_content = generate_opcodes_header () in
    
    (* Return tuple (ops_content, main_content, opcodes_header_content) *)
    (ops_file_content, main_file_content, opcodes_header_content)

  (****************************************************************************)
  (* compile_ast - Main Entry Point                                           *)
  (*                                                                          *)
  (* Extracts structural info from ORIGINAL Sail AST (before rewrites):       *)
  (* 1. Union clauses (RTYPE, ITYPE, etc.) - instruction families             *)
  (* 2. Enum literals (ADD, SUB, etc.) - operation types                      *)
  (* 3. Mapping definitions (encdec) - opcode bit patterns                    *)
  (* 4. Execute function clauses - semantic expressions                       *)
  (*                                                                          *)
  (* Then generates CodAL with REAL semantic translation from execute AST.    *)
  (****************************************************************************)
  let compile_ast _env _effects basename ast _sail_source =
    (* Collect union clauses - instruction families *)
    let union_info = collect_union_clauses ast.defs in
    
    (* Collect enum literals - operation types *)
    let enum_info = collect_enum_literals ast.defs in
    
    (* Collect mappings - encdec bit patterns *)
    let mapping_info = collect_mappings ast.defs in
    
    (* Generate CodAL *)
    let (ops_content, main_content, opcodes_header_content) = 
      ast_to_codal union_info enum_info mapping_info ast.defs in
    
    (* Determine output directory *)
    let output_dir = 
      let try_paths = ["../../codal_plugin"; "../codal_plugin"; "codal_plugin"] in
      let rec find_dir = function
        | [] -> ""
        | path :: rest ->
            (try
              if Sys.file_exists path && Sys.is_directory path then
                path ^ "/"
              else
                find_dir rest
            with _ -> find_dir rest)
      in
      find_dir try_paths
    in
    
    (* Write the ops file (isa_ops.codal) *)
    let ops_filename = output_dir ^ "isa_ops.codal" in
    let ops_out = open_out ops_filename in
    output_string ops_out ops_content;
    flush ops_out;
    close_out ops_out;
    
    (* Write the opcodes header file (opcodes.hcodal) *)
    let opcodes_filename = output_dir ^ "opcodes.hcodal" in
    let opcodes_out = open_out opcodes_filename in
    output_string opcodes_out opcodes_header_content;
    flush opcodes_out;
    close_out opcodes_out;
    
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

