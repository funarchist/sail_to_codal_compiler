open Libsail

open Ast
open Ast_util (*string_of_id comes from here*)
open Ast_defs
open Type_check

module type CODALGEN_CONFIG = sig
  val generate_header : bool
  val header_includes : string list
end

module IdMap = Map.Make (struct
  type t = id
  let compare = Id.compare
end)

type operand_type = [`Register | `Immediate | `Enum | `Other]

type operand_info = {
  op_name : string;           (* Variable name from AST: rs1, rs2, rd, imm *)
  op_type : operand_type;     (* REGISTER, IMMEDIATE, ENUM, OTHER *)
  op_typ : typ;              (* Full Sail type *)
  op_position : int;          (* Position in constructor args *)
  op_bit_width : int option;  (* For immediates: bits(12) -> Some 12 *)
  op_signed : bool option;    (* For immediates: Some true/false or None *)
}

type union_clause_info = {
  uc_constructor : id;  (*RTYPE*)
  uc_args : typ list;    (*[Typ_regidx; Typ_regidx; Typ_regidx; Typ_rop];, additional for enum types*)
  uc_loc : Parse_ast.l;
  uc_operands : operand_info list option;  (* NEW: Extracted operand info (None = not yet extracted) *)
}

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
      let clause_info = { uc_constructor = constructor_id; uc_args = args; uc_loc = loc; uc_operands = None } in
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

type 'a mapping_info = {
  mi_id : id;
  mi_clauses : 'a mapcl list;
}

type 'a mapping_collection = 'a mapping_info IdMap.t  (* map from mapping ID to its info *)
let collect_mappings defs =
  let handle_def acc = function
    | DEF_aux (DEF_mapdef (MD_aux (MD_mapping (map_id, _, mapcls), _)), _) ->
        let mapping_info = { mi_id = map_id; mi_clauses = mapcls } in
        IdMap.add map_id mapping_info acc
    | DEF_aux (DEF_scattered (SD_aux (SD_mapcl (map_id, mapcl), _)), _) ->
        let existing = match IdMap.find_opt map_id acc with
          | Some info -> { info with mi_clauses = mapcl :: info.mi_clauses }
          | None -> { mi_id = map_id; mi_clauses = [mapcl] }
        in
        IdMap.add map_id existing acc
    | DEF_aux (_, _) -> acc
  in
  List.fold_left handle_def IdMap.empty defs


module Codalgen (Config : CODALGEN_CONFIG) = struct
  let extract_variable_names_from_pattern (left_mpexp : 'b mpexp) : string list =
    let extract_from_mpat mpat =
      match mpat with
      | MP_aux (MP_app (_constructor_id, args), _) ->
          (* Extract variable names from arguments, skipping the last (enum) *)
          let args_without_enum = 
            if List.length args > 0 then
              List.rev (List.tl (List.rev args))
            else
              []
          in
          List.filter_map (fun arg ->
            match arg with
            | MP_aux (MP_id id, _) ->
                (* Variable name - use directly from AST *)
                Some (string_of_id id)
            | MP_aux (MP_app (_, _), _) ->
                (* Function call - skip *)
                None
            | _ -> None
          ) args_without_enum
      | _ -> []
    in
    match left_mpexp with
    | MPat_aux (MPat_pat mpat, _) -> extract_from_mpat mpat
    | MPat_aux (MPat_when (mpat, _guard), _) -> extract_from_mpat mpat
  
  let extract_operand_info_from_clause 
      (clause : union_clause_info) 
      (left_mpexp : 'b mpexp) 
      : operand_info list =
    let var_names = extract_variable_names_from_pattern left_mpexp in
    
    let args_without_enum = match clause.uc_args with
      | [] -> []
      | args -> 
          let len = List.length args in
          if len > 0 then
            List.rev (List.tl (List.rev args))
          else
            []
    in
    
    let classify_operand idx typ var_names_remaining =
      match (typ, var_names_remaining) with
      | (Typ_aux (Typ_id id, _), var_name :: rest) when string_of_id id = "regidx" ->
          Some ({
            op_name = var_name;
            op_type = `Register;
            op_typ = typ;
            op_position = idx;
            op_bit_width = None;
            op_signed = None;
          }, rest)
      | (Typ_aux (Typ_app (bits_id, [A_aux (A_nexp (Nexp_aux (Nexp_constant width, _)), _)]), _), var_name :: rest)
          when string_of_id bits_id = "bits" ->
          let width_int = Big_int.to_int width in
          Some ({
            op_name = var_name;
            op_type = `Immediate;
            op_typ = typ;
            op_position = idx;
            op_bit_width = Some width_int;
            op_signed = None;  (* Will be inferred from usage context *)
          }, rest)
      | (Typ_aux (Typ_id _id, _), _) ->
          None
      | (_, var_name :: rest) ->
          Some ({
            op_name = var_name;
            op_type = `Other;
            op_typ = typ;
            op_position = idx;
            op_bit_width = None;
            op_signed = None;
          }, rest)
      | _ -> None
    in
    
    let rec match_types_with_names types names acc =
      match (types, names) with
      | (typ :: types_rest, _) ->
          (match classify_operand (List.length acc) typ names with
           | Some (operand, names_rest) -> 
               match_types_with_names types_rest names_rest (operand :: acc)
           | None -> 
               match_types_with_names types_rest names acc)
      | ([], _) -> List.rev acc
    in
    
    match_types_with_names args_without_enum var_names []

  let rec extract_reg_names_from_expression (exp : 'a exp) : string list =
    let E_aux (exp_aux, _) = exp in
    match exp_aux with
    | E_app_infix (e1, op_id, e2) when string_of_id op_id = "^" ->
        let left_names = extract_reg_names_from_expression e1 in
        let right_names = extract_reg_names_from_expression e2 in
        left_names @ right_names
    | E_app (func_id, [arg_exp]) when string_of_id func_id = "reg_name" ->
        (match arg_exp with
         | E_aux (E_id arg_id, _) -> [string_of_id arg_id]
         | _ -> [])
    | E_app (_, _) -> []
    | E_lit _ -> []
    | E_id _ -> []
    | E_block exps -> List.flatten (List.map extract_reg_names_from_expression exps)
    | E_tuple exps -> List.flatten (List.map extract_reg_names_from_expression exps)
    | E_if (_, then_exp, else_exp) ->
        let then_names = extract_reg_names_from_expression then_exp in
        let else_names = extract_reg_names_from_expression else_exp in
        then_names @ else_names
    | _ -> []  (* Other expression types - skip *)
  
  let rec extract_reg_names_from_mpat (mpat : 'b mpat) : string list =
    match mpat with
    | MP_aux (MP_string_append mpats, _) ->
        (* String concatenation: recursively extract from all sub-patterns *)
        List.flatten (List.map extract_reg_names_from_mpat mpats)
    | MP_aux (MP_app (func_id, [arg_mpat]), _) when string_of_id func_id = "reg_name" ->
        (* Function call: reg_name(id) - extract the argument *)
        (match arg_mpat with
         | MP_aux (MP_id arg_id, _) -> [string_of_id arg_id]
         | _ -> [])
    | MP_aux (MP_app (_, _), _) ->
        (* Other function calls (like spc(), sep(), hex_bits_signed_12(...)) - skip *)
        []
    | MP_aux (MP_lit _, _) ->
        (* String literals - skip *)
        []
    | MP_aux (MP_id _, _) ->
        (* Identifier (like mnemonic variable) - skip *)
        []
    | MP_aux (MP_tuple mpats, _) ->
        (* Tuple - recursively extract from all sub-patterns *)
        List.flatten (List.map extract_reg_names_from_mpat mpats)
    | MP_aux (MP_list mpats, _) ->
        (* List - recursively extract from all sub-patterns *)
        List.flatten (List.map extract_reg_names_from_mpat mpats)
    | MP_aux (MP_cons (mpat1, mpat2), _) ->
        (* Cons - recursively extract from both *)
        let names1 = extract_reg_names_from_mpat mpat1 in
        let names2 = extract_reg_names_from_mpat mpat2 in
        names1 @ names2
    | MP_aux (MP_vector mpats, _) ->
        (* Vector - recursively extract from all sub-patterns *)
        List.flatten (List.map extract_reg_names_from_mpat mpats)
    | MP_aux (MP_vector_concat mpats, _) ->
        (* Vector concatenation - recursively extract from all sub-patterns *)
        List.flatten (List.map extract_reg_names_from_mpat mpats)
    | MP_aux (MP_typ (mpat, _), _) ->
        (* Type annotation - extract from inner pattern *)
        extract_reg_names_from_mpat mpat
    | MP_aux (MP_as (mpat, _), _) ->
        (* As pattern - extract from inner pattern *)
        extract_reg_names_from_mpat mpat
    | _ -> []  (* Other pattern types - skip *)
  
  let extract_assembly_order (assembly_clause : 'b mapcl) : string list option =
    match assembly_clause with
    | MCL_aux (MCL_bidir (left_mpexp, right_mpexp), _) ->
        (* Try to extract expression from right_mpexp *)
        (* The right side is a mapping pattern (mpexp) that may contain MP_string_append *)
        (match right_mpexp with
         | MPat_aux (MPat_pat mpat, _) ->
             let reg_names = extract_reg_names_from_mpat mpat in
             if reg_names <> [] then (
               Some reg_names
             ) else (
               (* Fallback: extract from left pattern *)
               let var_names = extract_variable_names_from_pattern left_mpexp in
               if var_names <> [] then (
                 Some var_names
               ) else (
                 None
               )
             )
         | MPat_aux (MPat_when (mpat, _), _) ->
             (* Pattern with guard - extract from pattern *)
             let reg_names = extract_reg_names_from_mpat mpat in
             if reg_names <> [] then (
               Some reg_names
             ) else (
               (* Fallback: extract from left pattern *)
               let var_names = extract_variable_names_from_pattern left_mpexp in
               if var_names <> [] then (
                 Some var_names
               ) else (
                 None
               )
             ))
    | MCL_aux (MCL_forwards pexp, _) ->
        (match pexp with
         | Pat_aux (Pat_exp (_, exp), _) ->
             let reg_names = extract_reg_names_from_expression exp in
             if reg_names <> [] then Some reg_names else None
         | Pat_aux (Pat_when (_, _, exp), _) ->
             let reg_names = extract_reg_names_from_expression exp in
             if reg_names <> [] then Some reg_names else None)
    | MCL_aux (MCL_backwards pexp, _) ->
        (* Similar to forwards *)
        (match pexp with
         | Pat_aux (Pat_exp (_, exp), _) ->
             let reg_names = extract_reg_names_from_expression exp in
             if reg_names <> [] then (
               Some reg_names
             ) else (
               None
             )
         | Pat_aux (Pat_when (_, _, exp), _) ->
             let reg_names = extract_reg_names_from_expression exp in
             if reg_names <> [] then (
               Some reg_names
             ) else (
               None
             ))
  
  let infer_immediate_type 
      (typ : typ) 
      (usage_context : 'a exp option) 
      : string * bool =
    match typ with
    | Typ_aux (Typ_app (bits_id, [A_aux (A_nexp (Nexp_aux (Nexp_constant width, _)), _)]), _)
      when string_of_id bits_id = "bits" ->
        let width_int = Big_int.to_int width in
        (* Infer signed/unsigned from usage context *)
        let is_signed = match usage_context with
          | Some (E_aux (E_app (func_id, _), _)) ->
              (* Check if function is sign_extend *)
              string_of_id func_id = "sign_extend"
          | Some (E_aux (E_app_infix (_, op, _), _)) ->
              (* Check if operator suggests signed operation *)
              let op_str = string_of_id op in
              op_str = "<_s" || op_str = ">=_s"
          | _ -> 
              (* Default: most immediates are signed, except for very large ones *)
              width_int <= 12  (* Small immediates are usually signed *)
        in
        let prefix = if is_signed then "simm" else "uimm" in
        (prefix ^ string_of_int width_int, is_signed)
    | _ -> 
        (* Default fallback *)
        ("simm12", true)

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

  let rec translate_shift_amount (exp : 'a exp) (var_map : (string * string) list) : string =
    let E_aux (exp_aux, _) = exp in
    match exp_aux with
    (* If it's a subrange like x[n..0], use (uint5)x cast instead *)
    | E_app (func_id, args) when string_of_id func_id = "subrange_bits" || string_of_id func_id = "vector_subrange" ->
        (match args with
         | [vec; _hi; _lo] -> Printf.sprintf "(uint5)%s" (translate_exp vec var_map)
         | _ -> translate_exp exp var_map)
    (* Otherwise just translate normally *)
    | _ -> translate_exp exp var_map


  and translate_exp (exp : 'a exp) (var_map : (string * string) list) : string =
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
         
         (* Arithmetic operations - translate to CodAL operators (no extra parens) *)
         | "add_bits" | "add_vec" | "add_atom" ->
             (match args with
              | [a; b] -> Printf.sprintf "%s + %s" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> Printf.sprintf "add(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         | "sub_vec" | "sub_bits" | "sub_atom" ->
             (match args with
              | [a; b] -> Printf.sprintf "%s - %s" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> Printf.sprintf "sub(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         
         (* Bitwise operations - translate to CodAL operators (no extra parens) *)
         | "xor_vec" | "xor_bits" ->
             (match args with
              | [a; b] -> Printf.sprintf "%s ^ %s" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> Printf.sprintf "xor(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         | "and_vec" | "and_bits" ->
             (match args with
              | [a; b] -> Printf.sprintf "%s & %s" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> Printf.sprintf "and(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         | "or_vec" | "or_bits" ->
             (match args with
              | [a; b] -> Printf.sprintf "%s | %s" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> Printf.sprintf "or(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         
         | "shift_bits_left" | "shiftl" ->
             (match args with
              | [a; b] -> 
                  let src = translate_exp a var_map in
                  let b_str = translate_exp b var_map in
                  (* Check if b_str is a source register variable (src1, src2, etc.) *)
                  (* Strip any existing cast to check the base variable name *)
                  let base_var = 
                    let cast_pattern = Str.regexp "(uint5)\\(([^)]+)\\)" in
                    if Str.string_match cast_pattern b_str 0 then
                      Str.matched_group 1 b_str
                    else
                      b_str
                  in
                  (* Check if base_var is exactly a source register name *)
                  let is_src_reg = Str.string_match (Str.regexp "^src[0-9]+$") base_var 0 in
                  let amt = 
                    if is_src_reg then
                      base_var  (* Don't cast source registers in RTYPE *)
                    else
                      (* If b_str already has a cast, use it; otherwise add cast *)
                      if Str.string_match (Str.regexp "(uint5)") b_str 0 then
                        b_str
                      else
                        translate_shift_amount b var_map
                  in
                  Printf.sprintf "%s << %s" src amt
              | _ -> Printf.sprintf "shiftl(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         | "shift_bits_right" | "shiftr" ->
             (match args with
              | [a; b] -> 
                  let src = translate_exp a var_map in
                  let b_str = translate_exp b var_map in
                  (* Check if b_str is a source register variable - don't cast it *)
                  let is_src_reg = Str.string_match (Str.regexp "src[0-9]+") b_str 0 in
                  let amt = 
                    if is_src_reg then
                      b_str  (* Don't cast source registers *)
                    else
                      translate_shift_amount b var_map
                  in
                  Printf.sprintf "%s >> %s" src amt
              | _ -> Printf.sprintf "shiftr(%s)" (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
         | "shift_bits_right_arith" | "arith_shiftr" ->
             (match args with
              | [src_exp; amt_exp] -> 
                  let src_str = translate_exp src_exp var_map in
                  let amt_str = translate_exp amt_exp var_map in
                  (* Check if amt_str is a source register variable - don't cast it *)
                  let is_src_reg = Str.string_match (Str.regexp "src[0-9]+") amt_str 0 in
                  let amt_final = 
                    if is_src_reg then
                      amt_str  (* Don't cast source registers *)
                    else
                      translate_shift_amount amt_exp var_map
                  in
                  Printf.sprintf "(int32)%s >> %s" src_str amt_final
              | _ -> "0")
         

         | "subrange_bits" | "vector_subrange" ->
             (match args with
              | [vec; hi; lo] -> 
                  let vec_str = translate_exp vec var_map in
                  let lo_str = translate_exp lo var_map in
                  (* Check if this is extracting lower bits (lo = 0) - use (uint5) cast instead *)
                  if lo_str = "0" then
                    Printf.sprintf "(uint5)%s" vec_str
                  else
                    Printf.sprintf "%s[%s..%s]" vec_str (translate_exp hi var_map) lo_str
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
         
         (* Bool to bits - comparison operators already produce 0/1, so just pass through *)
         (* If it's wrapping a comparison that already has ? 1 : 0, don't double it *)
         | "bool_to_bits" ->
             (match args with
              | [arg] -> translate_exp arg var_map  (* Just pass through, comparisons handle ? 1 : 0 *)
              | _ -> "0")
         
         (* Comparison operators wrapped in functions - generate ternary for now, will be converted to if-else later *)
         (* Signed less than - note: string_of_id wraps operators in parens *)
         | "(operator <_s)" | "operator <_s" | "<_s" | "lt_int" | "signed_lt" ->
             (match args with
              | [a; b] -> Printf.sprintf "((int32)%s < (int32)%s) ? 1 : 0" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> "0")
         (* Unsigned less than *)
         | "(operator <_u)" | "operator <_u" | "<_u" | "lt_bits" | "unsigned_lt" ->
             (match args with
              | [a; b] -> Printf.sprintf "((uint32)%s < (uint32)%s) ? 1 : 0" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> "0")
         (* Signed greater or equal *)
         | "(operator >=_s)" | "operator >=_s" | ">=_s" | "gteq_int" | "signed_gteq" ->
             (match args with
              | [a; b] -> Printf.sprintf "((int32)%s >= (int32)%s) ? 1 : 0" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> "0")
         (* Unsigned greater or equal *)
         | "(operator >=_u)" | "operator >=_u" | ">=_u" | "gteq_bits" | "unsigned_gteq" ->
             (match args with
              | [a; b] -> Printf.sprintf "((uint32)%s >= (uint32)%s) ? 1 : 0" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> "0")
         (* Equality *)
         | "eq_bits" | "eq_int" | "==" ->
             (match args with
              | [a; b] -> Printf.sprintf "(%s == %s) ? 1 : 0" (translate_exp a var_map) (translate_exp b var_map)
              | _ -> "0")
         (* Inequality *)
         | "neq_bits" | "neq_int" | "!=" ->
             (match args with
              | [a; b] -> Printf.sprintf "(%s != %s) ? 1 : 0" (translate_exp a var_map) (translate_exp b var_map)
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
         
         (* Bitvector concatenation - concatenate the translated args *)
         (* For UTYPE, imm @ 0x000 should be imm << 12 *)
         | "bitvector_concat" | "append" | "@" ->
             (match args with
              | [a; b] -> 
                  let a_str = translate_exp a var_map in
                  let b_str = translate_exp b var_map in
                  (* Check if this is UTYPE pattern: imm @ 0x000 -> imm << 12 *)
                  if b_str = "0x000" || b_str = "0" then
                    Printf.sprintf "(%s << 12)" a_str
                  else
                    Printf.sprintf "(%s @ %s)" a_str b_str
              | _ -> String.concat " @ " (List.map (fun a -> translate_exp a var_map) args))
         
         (* Default: preserve function call but still translate args *)
         | _ -> Printf.sprintf "%s(%s)" func_name (String.concat ", " (List.map (fun a -> translate_exp a var_map) args)))
    
    (* Binary operations *)
    | E_app_infix (left, op_id, right) ->
        let op_name = string_of_id op_id in
        let left_str = translate_exp left var_map in
        let right_str = translate_exp right var_map in
        (* Handle comparison operators with proper ? 1 : 0 suffix *)
        if op_name = "<_s" || op_name = ">=_s" then
          Printf.sprintf "((int32)%s %s (int32)%s) ? 1 : 0" left_str 
            (if op_name = "<_s" then "<" else ">=") right_str
        else if op_name = "<_u" || op_name = ">=_u" then
          Printf.sprintf "((uint32)%s %s (uint32)%s) ? 1 : 0" left_str 
            (if op_name = "<_u" then "<" else ">=") right_str
        else if op_name = "==" || op_name = "!=" then
          Printf.sprintf "(%s %s %s) ? 1 : 0" left_str op_name right_str
        else
          let op_str = match op_name with
            | "+" -> "+"
            | "-" -> "-"
            | "&" -> "&"
            | "|" -> "|"
            | "^" -> "^"
            | "<<" -> "<<"
            | ">>" -> ">>"
            | _ -> op_name
          in
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
    
    (* Let binding - extract pattern variable and add to var_map *)
    | E_let (LB_aux (LB_val (pat, bind_exp), _), body) ->
        let bind_str = translate_exp bind_exp var_map in
        (* Extract variable name(s) from pattern *)
        let rec extract_pat_vars p = 
          match p with
          | P_aux (P_id id, _) -> [string_of_id id]
          | P_aux (P_typ (_, inner_pat), _) -> extract_pat_vars inner_pat
          | P_aux (P_tuple pats, _) -> List.concat_map extract_pat_vars pats
          | P_aux (P_wild, _) -> []  (* Wildcard - no binding *)
          | P_aux (P_lit _, _) -> []  (* Literal pattern - no binding *)
          | _ -> []
        in
        let bound_vars = extract_pat_vars pat in
        (* Add bound variables to var_map, mapping them to their translated binding *)
        let updated_var_map = 
          match bound_vars with
          | [var_name] -> 
              (* Single variable - map it to the translated binding expression *)
              (var_name, bind_str) :: var_map
          | _ -> 
              (* Multiple variables (tuple) or none - keep var_map as is *)
              var_map
        in
        translate_exp body updated_var_map
    
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
    
    (* Let binding: search BOTH the binding expression AND the body *)
    (* Also update var_map with the bound variable for proper translation *)
    | E_let (LB_aux (LB_val (pat, bind_exp), _), body) ->
        (* First, search in the binding expression (e.g., let taken = match op {...}) *)
        (match find_match_arm_for_enum bind_exp enum_value_id var_map with
         | Some result -> Some result
         | None ->
             (* If not found in binding, search in body with updated var_map *)
             (* Extract variable name from pattern *)
             let bound_var = 
               match pat with
               | P_aux (P_id id, _) -> Some (string_of_id id)
               | P_aux (P_typ (_, P_aux (P_id id, _)), _) -> Some (string_of_id id)
               | _ -> None
             in
             (* Translate binding and update var_map *)
             let bind_str = translate_exp bind_exp var_map in
             let updated_var_map = match bound_var with
               | Some var_name -> (var_name, bind_str) :: var_map
               | None -> var_map
             in
             find_match_arm_for_enum body enum_value_id updated_var_map)
    
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
  let translate_execute_for_case constructor_name (enum_value_id : id) 
      execute_clauses 
      (operand_names : string list) : string =
    (* Find ALL execute clauses for this constructor (there may be multiple) *)
    let all_matching_clauses = List.filter_map (fun (_func_id, pexp) ->
      match parse_execute_clause pexp with
      | Some (constr_id, arg_ids, body) when string_of_id constr_id = constructor_name ->
          Some (arg_ids, body)
      | _ -> None
    ) execute_clauses in
    
    match all_matching_clauses with
    | [] -> 
        (* No execute clause found - generate placeholder *)
        Printf.sprintf "/* TODO: translate execute for %s.%s */" 
          constructor_name (string_of_id enum_value_id)
    | (arg_ids, body) :: _ ->
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
        
        (* Search through ALL matching clauses to find one that contains this enum value *)
        let rec search_clauses = function
          | [] -> None
          | (_, body) :: rest ->
              (match find_match_arm_for_enum body enum_value_id var_map with
               | Some arm_translation -> Some arm_translation
               | None -> search_clauses rest)
        in
        
        (match search_clauses all_matching_clauses with
         | Some arm_translation -> arm_translation
         | None -> 
             (* Fallback: translate whole body from first clause *)
             translate_exp body var_map)

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
    
    (* Helper: Extract binary literal value from mpat *)
    let extract_bin_literal_from_mpat (mpat : 'b mpat) : (string * int) option =
      match mpat with
      | MP_aux (MP_lit (L_aux (L_bin bits, _)), _) ->
          (try Some (bits, int_of_string ("0b" ^ bits)) with _ -> None)
      | MP_aux (MP_lit (L_aux (L_hex hex, _)), _) ->
          (try Some (hex, int_of_string ("0x" ^ hex)) with _ -> None)
        | _ -> None
    in

    let extract_pattern_parts_from_concat (mpexp : 'b mpexp) : (string list * (int option * int option * int option)) =
      (* Helper to extract from mpat (vector concat or single) *)
      let extract_from_vector_concat pats =
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
        
        let func7_opt = 
          (* First 7-bit literal (index 0) for RTYPE *)
          match List.find_opt (fun (i, bits, _) -> i = 0 && String.length bits = 7) indexed_literals with
          | Some (_, _, value) -> Some value
          | None -> 
              (* Also check for 6-bit func7 (used by SHIFTIOP) - treat as 7-bit with leading 0 *)
              match List.find_opt (fun (i, bits, _) -> i = 0 && String.length bits = 6) indexed_literals with
              | Some (_, _, value) -> Some value  (* 6-bit value, will be treated as 7-bit *)
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
          | [] -> 
              (* If no 7-bit literal found, check for helper mapping function calls at the end *)
              (* encdec_uop is a 7-bit opcode field (others like encdec_iop, encdec_bop, encdec_sop are 3-bit func3) *)
              let last_pat = List.nth_opt pats (List.length pats - 1) in
              (match last_pat with
               | Some (MP_aux (MP_app (id, _), _)) ->
                   let id_str = string_of_id id in
                   if id_str = "encdec_uop" then
                     (* Treat as 7-bit opcode field (value doesn't matter for width computation) *)
                     Some 0  (* Dummy value - we only care about the width, not the actual value *)
                   else None
               | _ -> None)
        in
        
        (all_parts, (func7_opt, func3_opt, opcode_opt))
      in
      
      (* Extract from mpat - handles vector_concat and single patterns *)
      let extract_from_mpat mpat =
        match mpat with
        | MP_aux (MP_vector_concat pats, _) -> extract_from_vector_concat pats
        | _ ->
            (* Single pattern - extract if it's a literal *)
            (match extract_bin_literal_from_mpat mpat with
             | Some (bits, value) ->
                 let len = String.length bits in
                 let func7_opt = if len = 7 then Some value else None in
                 let func3_opt = if len = 3 then Some value else None in
                 let opcode_opt = if len = 7 then Some value else None in
                 (["0b" ^ bits], (func7_opt, func3_opt, opcode_opt))
             | None -> ([], (None, None, None)))
      in
      
      (* Main extraction - handle both MPat_pat and MPat_when *)
      match mpexp with
      | MPat_aux (MPat_pat mpat, _) -> extract_from_mpat mpat
      | MPat_aux (MPat_when (mpat, _guard), _) -> extract_from_mpat mpat  (* Handle when clause *)
    in
    
    (* Helper: Convert integer to binary string with specified width *)
    let int_to_binary_string value width =
      let rec to_bin n w acc =
        if w <= 0 then acc
        else to_bin (n lsr 1) (w - 1) (string_of_int (n land 1) ^ acc)
      in
      "0b" ^ to_bin value width ""
    in
    
    let compute_opcode_value (func7_opt, func3_opt, opcode_opt) constructor_name : string option =
      (* Calculate width from field presence (same logic as compute_opcode_width) *)
      (* func7: 7 bits (or 6 bits for SHIFTIOP, padded to 7), func3: 3 bits, opcode: 7 bits *)
      let func7_width = 
        match func7_opt with
        | Some _ -> 
            (* Check if it's 6-bit func7 (SHIFTIOP) - pad to 7 bits *)
            if constructor_name = "SHIFTIOP" || constructor_name = "IMM_SHIFT" then 7
            else 7
        | None -> 0
      in
      let func3_width = match func3_opt with Some _ -> 3 | None -> 0 in
      let opcode_width = match opcode_opt with Some _ -> 7 | None -> 0 in
      let total_width = func7_width + func3_width + opcode_width in
      
      (* Calculate shifts based on field presence (not hardcoded) *)
      (* func7 shift = func3_width + opcode_width = 3 + 7 = 10 (if both present) *)
      (* func3 shift = opcode_width = 7 (if opcode present) *)
      (* opcode shift = 0 *)
      let func7_shift = func3_width + opcode_width in
      let func3_shift = opcode_width in
      
      (* Compute opcode value based on which fields are present *)
      match (func7_opt, func3_opt, opcode_opt) with
      | (Some func7, Some func3, Some opc) ->
          (* All three fields present: func7 @ func3 @ opcode *)
          (* Special case: SHIFTIOP has 6-bit func7 that needs padding to 7-bit *)
          let func7_final = 
            if constructor_name = "SHIFTIOP" || constructor_name = "IMM_SHIFT" then
              (* Check if func7 is 6-bit (value < 64) and pad it *)
              if func7 < 64 then func7 lsl 1  (* 6-bit -> 7-bit with leading 0 *)
              else func7
            else
              func7
          in
          let full_value = (func7_final lsl func7_shift) lor (func3 lsl func3_shift) lor opc in
          Some (int_to_binary_string full_value total_width)
      | (None, Some func3, Some opc) ->
          (* func3 and opcode only: func3 @ opcode *)
          let full_value = (func3 lsl func3_shift) lor opc in
          Some (int_to_binary_string full_value total_width)
      | (None, None, Some opc) ->
          (* opcode only *)
          Some (int_to_binary_string opc total_width)
      | _ -> None
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
    
    (* Helper: Extract size_enc mapping (word_width -> bits(2)) *)
    (* Returns list of (enum_id, bit_value) where enum_id is BYTE, HALF, WORD, DOUBLE *)
    let get_size_enc_mapping () : (id * int) list =
      let size_enc_id = mk_id "size_enc" in
      match IdMap.find_opt size_enc_id mapping_info with
      | Some info ->
          List.filter_map (fun mapcl ->
            match mapcl with
            | MCL_aux (MCL_bidir (left_mpexp, right_mpexp), _) ->
                (* Left: word_width enum (BYTE, HALF, WORD, DOUBLE), Right: bits(2) *)
                let enum_opt = match left_mpexp with
                  | MPat_aux (MPat_pat (MP_aux (MP_id id, _)), _) -> Some id
                  | _ -> None
                in
                let value_opt = match extract_bit_literal right_mpexp with
                  | Some (bits, v) when String.length bits = 2 -> Some v
                  | Some (bits, v) when String.length bits <= 2 -> Some v  (* Handle padding *)
                  | _ -> None
                in
                (match (enum_opt, value_opt) with
                 | (Some e, Some v) -> Some (e, v)
                 | _ -> None)
            | _ -> None
          ) info.mi_clauses
      | None -> []
    in
    
    (* Helper: Extract bool_bits mapping (bool -> bits(1)) *)
    (* Returns: (true_value, false_value) *)
    let get_bool_bits_mapping () : (int * int) option =
      let bool_bits_id = mk_id "bool_bits" in
      match IdMap.find_opt bool_bits_id mapping_info with
      | Some info ->
          let true_val = ref None in
          let false_val = ref None in
          List.iter (fun mapcl ->
            match mapcl with
            | MCL_aux (MCL_bidir (left_mpexp, right_mpexp), _) ->
                (* Left: bool literal, Right: bits(1) *)
                let bool_opt = match left_mpexp with
                  | MPat_aux (MPat_pat (MP_aux (MP_lit (L_aux (L_true, _)), _)), _) -> Some true
                  | MPat_aux (MPat_pat (MP_aux (MP_lit (L_aux (L_false, _)), _)), _) -> Some false
                  | _ -> None
                in
                let value_opt = match extract_bit_literal right_mpexp with
                  | Some (bits, v) when String.length bits = 1 -> Some v
                  | Some (bits, v) when String.length bits <= 1 -> Some v
                  | _ -> None
                in
                (match (bool_opt, value_opt) with
                 | (Some true, Some v) -> true_val := Some v
                 | (Some false, Some v) -> false_val := Some v
                 | _ -> ())
            | _ -> ()
          ) info.mi_clauses;
          (match (!true_val, !false_val) with
           | (Some t, Some f) -> Some (t, f)
           | _ -> None)
      | None -> None
    in
    
    (* Helper: Extract word_width enum values *)
    let get_word_width_enum_values () : id list =
      let word_width_id = mk_id "word_width" in
      match IdMap.find_opt word_width_id enum_info with
      | Some ids -> ids
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
          (* Handle both MPat_pat (simple) and MPat_when (with guard clause) *)
          let extract_from_pattern (mpexp : 'b mpexp) =
            let extract_from_mpat mpat =
              match mpat with
              | MP_aux (MP_app (constructor_id, args), _) ->
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
            match mpexp with
            | MPat_aux (MPat_pat mpat, _) -> extract_from_mpat mpat
            | MPat_aux (MPat_when (mpat, _guard), _) -> extract_from_mpat mpat  (* Handle when clause *)
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
                 (* Special handling for LOAD/STORE with function calls (size_enc, bool_bits) *)
                 (* For LOAD/STORE, if enum_value_id is "width", it means we have a parametric encoding *)
                 let is_load_store_with_vars = 
                   (constructor_name = "LOAD" || constructor_name = "STORE") && 
                   string_of_id enum_value_id = "width"
                 in
                 if is_load_store_with_vars then begin
                     (* Get mappings *)
                     let size_enc_map = get_size_enc_mapping () in
                     let _bool_bits_map = get_bool_bits_mapping () in  (* Reserved for future use - currently using hardcoded values *)
                     let word_width_enums = get_word_width_enum_values () in
                     
                     (* If mappings are empty, we can't expand - this shouldn't happen but handle gracefully *)
                     if size_enc_map = [] || word_width_enums = [] then begin
                       []
                     end else begin
                     
                     (* Generate all valid combinations *)
                     let load_store_results = if constructor_name = "LOAD" then begin
                       (* LOAD: expand (width, is_unsigned) combinations *)
                       let base_opcode = match opcode_opt with Some v -> v | None -> 0b0000011 in
                       let results = ref [] in
                       List.iter (fun width_enum ->
                         let width_name = string_of_id width_enum in
                         (* Find matching entry by comparing string names, not ID equality *)
                         let size_enc_val = List.find_opt (fun (id, _) -> 
                           string_of_id id = width_name
                         ) size_enc_map |> Option.map snd in
                         (match size_enc_val with
                          | Some size_val ->
                              (* Generate signed and unsigned variants *)
                              (* TODO: Use bool_bits_map instead of hardcoded [(false, 0); (true, 1)] *)
                              List.iter (fun (is_unsigned, unsigned_val) ->
                                (* Check valid_load_encdec constraint *)
                                (* For RV32: unsigned only for widths < 4 bytes, signed for widths <= 4 bytes *)
                                let width_bytes = match width_name with
                                  | "BYTE" -> 1 | "HALF" -> 2 | "WORD" -> 4 | "DOUBLE" -> 8 | _ -> 4
                                in
                                let is_valid = if is_unsigned then width_bytes < 4 else width_bytes <= 4 in
                                if is_valid then begin
                                  (* Compute func3: bool_bits(is_unsigned) @ size_enc(width) *)
                                  (* func3[2] = bool_bits(is_unsigned), func3[1:0] = size_enc(width) *)
                                  let func3_val = (unsigned_val lsl 2) lor size_val in
                                  let full_opcode = (func3_val lsl 7) lor base_opcode in
                                  (* Generate instruction name: lb, lbu, lh, lhu, lw *)
                                  let inst_name = match (width_name, is_unsigned) with
                                    | ("BYTE", false) -> "lb"
                                    | ("BYTE", true) -> "lbu"
                                    | ("HALF", false) -> "lh"
                                    | ("HALF", true) -> "lhu"
                                    | ("WORD", false) -> "lw"
                                    | ("WORD", true) -> "lwu"  (* RV64 only, but include for completeness *)
                                    | ("DOUBLE", false) -> "ld"  (* RV64 only *)
                                    | _ -> "l?"
                                  in
                                  (* Use ITYPE prefix for LOAD instructions *)
                                  let enum_name = Printf.sprintf "ITYPE_%s" (String.uppercase_ascii inst_name) in
                                  let enum_id = mk_id enum_name in
                                  results := { oi_constructor = constructor_id;
                                              oi_enum_value = enum_id;
                                              oi_bit_pattern = String.concat " " pattern_parts;
                                              oi_func7 = None;
                                              oi_func3 = Some (int_to_binary_string func3_val 3);
                                              oi_opcode = Some (int_to_binary_string base_opcode 7);
                                              oi_computed_value = Some (int_to_binary_string full_opcode 10) } :: !results
                                end
                              ) [(false, 0); (true, 1)]
                          | None -> ())
                       ) word_width_enums;
                       !results
                     end else begin
                       (* STORE: expand width combinations *)
                       let base_opcode = match opcode_opt with Some v -> v | None -> 0b0100011 in
                       let results = ref [] in
                       List.iter (fun width_enum ->
                         let width_name = string_of_id width_enum in
                         (* Find matching entry by comparing string names, not ID equality *)
                         let size_enc_val = List.find_opt (fun (id, _) -> 
                           string_of_id id = width_name
                         ) size_enc_map |> Option.map snd in
                         (match size_enc_val with
                          | Some size_val ->
                              (* STORE func3: 0b0 @ size_enc(width) *)
                              (* func3[2] = 0, func3[1:0] = size_enc(width) *)
                              let func3_val = size_val in  (* First bit is 0, so just size_val *)
                              let full_opcode = (func3_val lsl 7) lor base_opcode in
                              (* Generate instruction name: sb, sh, sw *)
                              let inst_name = match width_name with
                                | "BYTE" -> "sb"
                                | "HALF" -> "sh"
                                | "WORD" -> "sw"
                                | "DOUBLE" -> "sd"  (* RV64 only *)
                                | _ -> "s?"
                              in
                              (* Use STYPE prefix for STORE instructions *)
                              let enum_name = Printf.sprintf "STYPE_%s" (String.uppercase_ascii inst_name) in
                              let enum_id = mk_id enum_name in
                              results := { oi_constructor = constructor_id;
                                          oi_enum_value = enum_id;
                                          oi_bit_pattern = String.concat " " pattern_parts;
                                          oi_func7 = None;
                                          oi_func3 = Some (int_to_binary_string func3_val 3);
                                          oi_opcode = Some (int_to_binary_string base_opcode 7);
                                          oi_computed_value = Some (int_to_binary_string full_opcode 10) } :: !results
                          | None -> ())
                       ) word_width_enums;
                       !results
                     end in
                     load_store_results
                     end
                   end else begin
                     (* Not LOAD/STORE with variables, try helper mapping *)
                     let helper_name = match constructor_name with
                       | "ITYPE" -> "encdec_iop"
                       | "BTYPE" -> "encdec_bop"
                       | "UTYPE" -> "encdec_uop"
                       | "SHIFTIOP" -> "encdec_sop"
                       | _ -> ""
                     in
                     let helper_results = if helper_name <> "" then begin
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
                               (* func7 (7 bits, padded from 6 bits) @ func3 @ opcode (17 bits total) *)
                               let base_opc = match opcode_opt with Some v -> v | None -> 0 in
                               let f7 = match func7_opt with Some v -> v | None -> 0 in
                               let f7_padded = f7 lsl 1 in  (* Pad 6-bit to 7-bit *)
                               let full = (f7_padded lsl 10) lor (entry_value lsl 7) lor base_opc in
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
                          oi_computed_value = None }] in
                     helper_results
                   end
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
          let results = List.concat_map parse_encdec_clause info.mi_clauses in
          results
      | None -> 
          []
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
    
    (* Helper: Find encdec clause for a constructor *)
    (* Returns the left pattern from encdec clause if found *)
    let find_encdec_left_pattern (constructor_id : id) : 'b mpexp option =
      match encdec_mapping with
      | Some info ->
          let rec find_in_list = function
            | [] -> None
            | mapcl :: rest ->
                match mapcl with
                | MCL_aux (MCL_bidir (left_mpexp, _), _) ->
                    (* Extract constructor from left pattern *)
                    let extract_constructor mpexp =
                      match mpexp with
                      | MPat_aux (MPat_pat (MP_aux (MP_app (id, _), _)), _) -> Some id
                      | MPat_aux (MPat_when (mpat, _), _) ->
                          (match mpat with
                           | MP_aux (MP_app (id, _), _) -> Some id
                           | _ -> None)
                      | _ -> None
                    in
                    (match extract_constructor left_mpexp with
                     | Some id when Id.compare id constructor_id = 0 -> Some left_mpexp
                     | _ -> find_in_list rest)
                | _ -> find_in_list rest
          in
          find_in_list info.mi_clauses
      | None -> None
    in
    
    (* Helper: Find assembly mapping clause for a constructor *)
    (* Returns the full mapping clause if found *)
    let find_assembly_clause (constructor_id : id) : 'b mapcl option =
      let assembly_map_id = mk_id "assembly" in
      match IdMap.find_opt assembly_map_id mapping_info with
      | Some info ->
          let rec find_in_list = function
            | [] -> None
            | mapcl :: rest ->
                match mapcl with
                | MCL_aux (MCL_bidir (left_mpexp, _), _) ->
                    (* Extract constructor from left pattern *)
                    let extract_constructor mpexp =
                      match mpexp with
                      | MPat_aux (MPat_pat (MP_aux (MP_app (id, _), _)), _) -> Some id
                      | MPat_aux (MPat_when (mpat, _), _) ->
                          (match mpat with
                           | MP_aux (MP_app (id, _), _) -> Some id
                           | _ -> None)
                      | _ -> None
                    in
                    (match extract_constructor left_mpexp with
                     | Some id when Id.compare id constructor_id = 0 -> Some mapcl
                     | _ -> find_in_list rest)
                | MCL_aux (MCL_forwards pexp, _) ->
                    (* Check if pattern matches constructor *)
                    (match pexp with
                     | Pat_aux (Pat_exp (P_aux (P_app (id, _), _), _), _) 
                     | Pat_aux (Pat_when (P_aux (P_app (id, _), _), _, _), _) ->
                         if Id.compare id constructor_id = 0 then Some mapcl
                         else find_in_list rest
                     | _ -> find_in_list rest)
                | MCL_aux (MCL_backwards pexp, _) ->
                    (* Similar to forwards *)
                    (match pexp with
                     | Pat_aux (Pat_exp (P_aux (P_app (id, _), _), _), _) 
                     | Pat_aux (Pat_when (P_aux (P_app (id, _), _), _, _), _) ->
                         if Id.compare id constructor_id = 0 then Some mapcl
                         else find_in_list rest
                     | _ -> find_in_list rest)
          in
          find_in_list info.mi_clauses
      | None -> None
    in
    
    (* Helper: Convert operand_info to (name, codal_type) tuple *)
    let operand_info_to_codal (op : operand_info) : (string * string) =
      let codal_type = match op.op_type with
        | `Register -> "xpr_all"
        | `Immediate ->
            (* Infer CodAL type from bit width and signedness *)
            (match (op.op_bit_width, op.op_signed) with
             | (Some 5, Some false) -> "uimm5"
             | (Some 12, Some true) -> "simm12"
             | (Some 12, Some false) -> "uimm12"
             | (Some 12, None) -> "simm12"  (* Default: signed *)
             | (Some 20, Some false) -> "uimm20"
             | (Some 20, Some true) -> "simm20"
             | (Some 20, None) -> "uimm20"  (* Default for 20-bit: unsigned *)
             | (Some width, _) ->
                 (* Generic fallback based on width *)
                 if width <= 12 then "simm12" else "uimm20"
             | _ -> "simm12")  (* Default fallback *)
        | `Enum -> "xpr_all"  (* Shouldn't happen, but handle gracefully *)
        | `Other -> "xpr_all"
      in
      (op.op_name, codal_type)
    in
    
    (* Helper: Determine operand names and types using Phase 1 extraction *)
    (* This replaces hardcoded operand mapping with AST-driven extraction *)
    let determine_operands (clause : union_clause_info) : (string * string) list =
      let constructor_id = clause.uc_constructor in
      (* Try to find encdec clause for this constructor *)
      match find_encdec_left_pattern constructor_id with
      | Some left_mpexp ->
          (* Use Phase 1 extraction functions *)
          let operand_info_list = extract_operand_info_from_clause clause left_mpexp in
          (* Convert to (name, codal_type) format *)
          List.map operand_info_to_codal operand_info_list
      | None ->
          (* Fallback: if encdec clause not found, use variable names from types *)
          (* This shouldn't happen in normal operation, but provides graceful degradation *)
          (* Filter out enum type (last argument) *)
          let args_without_enum = match clause.uc_args with
            | [] -> []
            | args -> 
                let len = List.length args in
                if len > 0 then
                  List.rev (List.tl (List.rev args))
                else
                  []
          in
          (* Generate generic operand names *)
          List.mapi (fun idx typ ->
            match typ with
            | Typ_aux (Typ_id id, _) when string_of_id id = "regidx" ->
                (Printf.sprintf "reg%d" idx, "xpr_all")
            | Typ_aux (Typ_app (bits_id, [A_aux (A_nexp (Nexp_aux (Nexp_constant width, _)), _)]), _)
              when string_of_id bits_id = "bits" ->
                let width_int = Big_int.to_int width in
                let codal_type = if width_int <= 12 then "simm12" else "uimm20" in
                ("imm", codal_type)
            | _ -> (Printf.sprintf "arg%d" idx, "xpr_all")
          ) args_without_enum
    in
    
    let map_family_name_with_suffix (constructor_name : string) : (string * string * string) =
      match constructor_name with
      | "RTYPE" -> ("RTYPE", "rtype_alu", "rtype_alu")
      | "SHIFTIOP" -> ("IMM_SHIFT", "shift_imm", "shift_imm")
      | "ITYPE" -> ("ITYPE", "itype_alu", "itype_alu")
      | "LOAD" -> ("ITYPE", "itype_loads", "itype_loads")  (* Merged into ITYPE but separate element *)
      | "STORE" -> ("STYPE", "stype_store", "stype_store")
      | "UTYPE" -> ("UTYPE", "utype_ops", "utype_ops")
      | "JAL" -> ("JTYPE", "jtype_jlink", "jtype_jlink")
      | "JALR" -> ("ITYPE", "itype_jlreg", "itype_jlreg")  (* Merged into ITYPE but separate element *)
      | "BTYPE" -> ("BTYPE", "btype_branches", "btype_branches")
      | _ -> (constructor_name, String.lowercase_ascii constructor_name, String.lowercase_ascii constructor_name)
    in
    
    (* Helper: Generate use declarations from operands *)
    let generate_use_declarations 
        (constructor_name : string)
        (operands : (string * string) list) 
        : (string * string * string list * (string * string) list) =
      (* Group operands by type for use declarations *)
      let register_ops = List.filter_map (fun (name, typ) ->
        if typ = "xpr_all" then Some name else None
      ) operands in
      let immediate_ops = List.filter_map (fun (name, typ) ->
        if typ <> "xpr_all" then Some (name, typ) else None
      ) operands in
      
      (* Generate use declarations - fix order for RTYPE/BTYPE to match reference *)
      (* AST gives [rs2, rs1, rd] but we want [rs1, rs2, rd] for proper mapping *)
      let reordered_regs = 
        if (constructor_name = "RTYPE" || constructor_name = "BTYPE" || constructor_name = "STORE") && List.length register_ops >= 2 then
          (* Reverse first two registers to get rs1, rs2 order *)
          let first = List.nth register_ops 1 in  (* rs1 *)
          let second = List.nth register_ops 0 in (* rs2 *)
          let rest = if List.length register_ops > 2 then [List.nth register_ops 2] else [] in
          [first; second] @ rest
        else if constructor_name = "SHIFTIOP" && List.length register_ops >= 2 then
          (* SHIFTIOP AST: [rd, rs1] -> we want [rs1, rd] *)
          let rd = List.nth register_ops 0 in
          let rs1 = List.nth register_ops 1 in
          [rs1; rd]
        else
          register_ops
      in
      let use_regs = if reordered_regs = [] then ""
                    else "    use xpr_all as " ^ (String.concat ", " reordered_regs) ^ ";\n" in
      let use_imms = String.concat "" (List.map (fun (name, typ) ->
        Printf.sprintf "    use %s as %s;\n" typ name
      ) immediate_ops) in
      
      (use_regs, use_imms, register_ops, immediate_ops)
    in
    
    (* Helper: Generate assembly syntax from AST *)
    let generate_assembly_syntax
        (clause : union_clause_info)
        (enum_values : id list)
        (use_decls : string list)
        : string =
      let mnemonic_var = if enum_values <> [] then "opc" else "\"unknown\"" in
      (* Try to extract assembly order from AST *)
      let operand_order_opt = match find_assembly_clause clause.uc_constructor with
        | Some assembly_clause ->
            (match extract_assembly_order assembly_clause with
             | Some order ->
                 Some order
             | None ->
                 None)
        | None ->
            None
      in
      let operand_str = 
        match operand_order_opt with
        | Some order ->
            (* Use extracted order - map operand names to use_decls *)
            (* Create a map from operand names to their positions in use_decls *)
            let operand_map = List.mapi (fun idx name -> (name, idx)) use_decls in
            (* Map extracted order to actual operand names, preserving order *)
            let mapped_order = List.filter_map (fun name ->
              List.find_opt (fun (n, _) -> n = name) operand_map
            ) order in
            (* Generate operand string from mapped order *)
            if mapped_order <> [] then
              String.concat " \",\" " (List.map (fun (name, _) -> name) mapped_order)
            else
              (* Fallback if mapping fails - use original order *)
              String.concat " \",\" " use_decls
        | None ->
            (* Should not happen - dynamic extraction should always succeed *)
            (* Use original order as last resort *)
            String.concat " \",\" " use_decls
      in
      Printf.sprintf "    assembly { %s %s };" mnemonic_var operand_str
    in

    let generate_binary_encoding_template 
        (constructor_name : string)
        (right_pattern : 'b mpexp)
        (left_pattern : 'b mpexp)
        (operands : operand_info list) : string option =
      (* Extract pattern parts from right-hand side *)
      let (pattern_parts, (_func7_opt, _func3_opt, _opcode_opt)) = 
        extract_pattern_parts_from_concat right_pattern
      in
      
      (* Extract variable names from left pattern to map operands *)
      let var_names = extract_variable_names_from_pattern left_pattern in
      
      (* Filter var_names to match operands (remove filtered-out variables like is_unsigned, width) *)
      (* Only include variables that correspond to actual operands *)
      let filtered_var_names = List.filter (fun var_name ->
        List.exists (fun op_info -> op_info.op_name = var_name) operands
      ) var_names in
      
      (* Create mapping from variable names to operand_info *)
      (* Ensure lists have same length before combining *)
      let operand_map = 
        if List.length filtered_var_names = List.length operands then
          List.combine filtered_var_names operands
        else (
          (* Fallback: try to match by name *)
          List.filter_map (fun op_info ->
            List.find_opt (fun vn -> vn = op_info.op_name) filtered_var_names
            |> Option.map (fun vn -> (vn, op_info))
          ) operands
        )
      in
      
      (* Track current bit position (from MSB to LSB, 31 down to 0) *)
      let rec build_encoding parts bit_pos operand_idx acc =
        match parts with
        | [] -> Some (String.concat " " (List.rev acc))
        | part :: rest ->
            (* Check if part is a bit literal *)
            if Str.string_match (Str.regexp "0b[01]+") part 0 then
              let bit_width = String.length part - 2 in  (* Subtract "0b" *)
              (* Determine if it's func7, func3, or opcode *)
              let encoding_part = 
                if bit_width = 7 && bit_pos = 31 then
                  (* First 7-bit literal at position 31-25 = func7 *)
                  "FUNC7(opc)"
                else if bit_width = 3 then
                  (* 3-bit literal = func3 *)
                  "FUNC3(opc)"
                else if bit_width = 7 && bit_pos <= 6 then
                  (* Last 7-bit literal at position 6-0 = opcode *)
                  "OPCODE(opc)"
                else
                  (* Other bit literal - keep as is for now *)
                  part
              in
              build_encoding rest (bit_pos - bit_width) operand_idx (encoding_part :: acc)
            else if Str.string_match (Str.regexp "<encdec_reg>") part 0 then
              (* Register operand - map to operand name *)
              if operand_idx < List.length operand_map then
                let (var_name, _op_info) = List.nth operand_map operand_idx in
                build_encoding rest (bit_pos - 5) (operand_idx + 1) (var_name :: acc)
              else
                build_encoding rest (bit_pos - 5) (operand_idx + 1) ("<reg>" :: acc)
            else if Str.string_match (Str.regexp "<.*>") part 0 then
              (* Other function call (like encdec_iop) - skip for now *)
              build_encoding rest bit_pos operand_idx acc
            else
              (* Variable name or other - try to map *)
              (match List.find_opt (fun (name, _) -> name = part) operand_map with
               | Some (_, op_info) ->
                   (* Check if it's an immediate that needs splitting *)
                   (* For STORE: imm is split into imm[11..5] and imm[4..0] *)
                   (* For BTYPE: imm is split into imm[11], imm[9..4], imm[3..0], imm[10] *)
                   (* For JAL: imm is split into imm[19], imm[9..0], imm[10], imm[18..11] *)
                   if op_info.op_type = `Immediate then
                     (* Check if this immediate needs splitting based on constructor *)
                     if constructor_name = "STORE" && bit_pos = 31 then
                       (* STORE: imm[11..5] at position 31-25 *)
                       let imm_name = op_info.op_name in
                       build_encoding rest (bit_pos - 7) operand_idx ((imm_name ^ "[11..5]") :: acc)
                     else if constructor_name = "STORE" && bit_pos = 11 then
                       (* STORE: imm[4..0] at position 11-7 *)
                       let imm_name = op_info.op_name in
                       build_encoding rest (bit_pos - 5) operand_idx ((imm_name ^ "[4..0]") :: acc)
                     else if constructor_name = "BTYPE" then
                       (* BTYPE has complex splitting - handle in special case *)
                       build_encoding rest bit_pos operand_idx acc
                     else if constructor_name = "JAL" then
                       (* JAL has complex splitting - handle in special case *)
                       build_encoding rest bit_pos operand_idx acc
                     else
                       (* Regular immediate - use as is *)
                       build_encoding rest bit_pos (operand_idx + 1) (op_info.op_name :: acc)
                   else
                     (* Register - use operand name *)
                     build_encoding rest (bit_pos - 5) (operand_idx + 1) (op_info.op_name :: acc)
               | None ->
                   (* Unknown part - skip *)
                   build_encoding rest bit_pos operand_idx acc)
      in
      
      (* Start building from MSB (position 31) *)
      build_encoding pattern_parts 31 0 []
    in
    
    (* Helper: Generate binary encoding from encdec pattern *)
    let generate_binary_encoding
        (constructor_name : string)
        (clause : union_clause_info)
        : string =
      (* Phase 2.2: Try to extract from encdec pattern *)
      let binary_encoding_from_pattern =
        match find_encdec_left_pattern clause.uc_constructor with
        | Some left_mpexp ->
            (* Find the corresponding right pattern from encdec clause *)
            let encdec_id = mk_id "encdec" in
            (match IdMap.find_opt encdec_id mapping_info with
             | Some info ->
                 let rec find_right_pattern = function
                   | [] -> None
                   | mapcl :: rest ->
                       match mapcl with
                       | MCL_aux (MCL_bidir (left, right), _) ->
                           (* Check if left matches *)
                           let extract_constructor mpexp =
                             match mpexp with
                             | MPat_aux (MPat_pat (MP_aux (MP_app (id, _), _)), _) -> Some id
                             | MPat_aux (MPat_when (mpat, _), _) ->
                                 (match mpat with
                                  | MP_aux (MP_app (id, _), _) -> Some id
                                  | _ -> None)
                             | _ -> None
                           in
                           (match extract_constructor left with
                            | Some id when Id.compare id clause.uc_constructor = 0 ->
                                Some right
                            | _ -> find_right_pattern rest)
                       | _ -> find_right_pattern rest
                 in
                 (match find_right_pattern info.mi_clauses with
                  | Some right_mpexp ->
                      (* Extract operand_info list from left pattern for generate_binary_encoding_template *)
                      let operand_info_list = extract_operand_info_from_clause clause left_mpexp in
                      (* Try to generate encoding template *)
                      (match generate_binary_encoding_template constructor_name right_mpexp left_mpexp operand_info_list with
                       | Some template ->
                           Some (Printf.sprintf "    binary { %s };" template)
                       | None ->
                           None)
                  | None ->
                      None)
             | None ->
                 None)
        | None ->
            None
      in
      (* Use generated template if available, otherwise error *)
      match binary_encoding_from_pattern with
      | Some template ->
          template
      | None ->
          (* Should not happen - dynamic generation should always succeed *)
          Printf.sprintf "    binary { /* ERROR: Could not generate binary encoding for %s */ };" constructor_name
    in
    
    (* Generate instruction element for a family *)
    let generate_instruction_element (clause : union_clause_info) : string =
      let constructor_name = string_of_id clause.uc_constructor in
      
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
        
        (* Generate use declarations *)
        let (use_regs, use_imms, register_ops, immediate_ops) = 
          generate_use_declarations constructor_name operands in
        let use_decls = List.map (fun (name, _) -> name) operands in
        
        (* Generate assembly syntax *)
        let assembly_syntax = 
          generate_assembly_syntax clause enum_values use_decls in
        
        (* Generate binary encoding *)
        let binary_encoding = 
          generate_binary_encoding constructor_name clause in
        
        (* Determine source registers (not destination) for local variable generation *)
        (* IMPORTANT: Correct mapping is rs1->src1, rs2->src2 to match reference isa.codal *)
        let (source_regs, dest_reg) = 
          let num_regs = List.length register_ops in
          if constructor_name = "RTYPE" && num_regs >= 3 then
            (* RTYPE from AST: [rs2, rs1, rd] - we need to REVERSE to get rs1, rs2 order *)
            (* src1 = rf_xpr_read(rs1), src2 = rf_xpr_read(rs2) *)
            let rs2 = List.nth register_ops 0 in
            let rs1 = List.nth register_ops 1 in
            let rd = List.nth register_ops 2 in
            ([rs1; rs2], Some rd)  (* Correct order: rs1 first, rs2 second *)
          else if constructor_name = "ITYPE" && num_regs >= 2 then
            (* ITYPE: rs1, rd -> source is rs1 *)
            ([List.nth register_ops 0], Some (List.nth register_ops 1))
          else if constructor_name = "LOAD" && num_regs >= 2 then
            (* LOAD: rs1, rd -> source is rs1, dest is rd *)
            ([List.nth register_ops 0], Some (List.nth register_ops 1))
          else if constructor_name = "JALR" && num_regs >= 2 then
            (* JALR: rs1, rd -> source is rs1, dest is rd *)
            ([List.nth register_ops 0], Some (List.nth register_ops 1))
          else if constructor_name = "SHIFTIOP" && num_regs >= 2 then
            (* SHIFTIOP AST: [rd, rs1] -> source is rs1, dest is rd *)
            let rd = List.nth register_ops 0 in
            let rs1 = List.nth register_ops 1 in
            ([rs1], Some rd)
          else if (constructor_name = "BTYPE" || constructor_name = "STORE") && num_regs >= 2 then
            (* BTYPE/STORE from AST: [rs2, rs1] - REVERSE to get rs1, rs2 order *)
            let rs2 = List.nth register_ops 0 in
            let rs1 = List.nth register_ops 1 in
            ([rs1; rs2], None)  (* Correct order: rs1 first, rs2 second *)
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
        (* Also add immediate operand mapping: shamt/imm -> immediate *)
        let operand_to_src_map = List.map (fun (reg, src) -> (reg, src)) src_var_map in
        let imm_var_map = List.filter_map (fun (name, _typ) ->
          (* Map immediate operand names to "immediate" local variable *)
          if name = "shamt" || name = "imm" then Some (name, "immediate")
          else None
        ) immediate_ops in
        let _full_var_map = operand_to_src_map @ imm_var_map in
        
        (* Generate switch cases using LOCAL VARIABLES *)
        (* Use target family prefix for enum names (e.g., ITYPE for LOAD, STYPE for STORE) *)
        let (target_family_for_switch, _, _) = map_family_name_with_suffix constructor_name in
        let target_family_prefix = String.uppercase_ascii target_family_for_switch in
        let switch_cases = List.map (fun enum_value_id ->
          let enum_value_name = string_of_id enum_value_id in
          (* Extract instruction name from enum_value (e.g., ITYPE_LB -> LB, STYPE_SB -> SB) *)
          let enum_upper = String.uppercase_ascii enum_value_name in
          let op_upper = 
            if String.length enum_upper > String.length target_family_prefix + 1 then
              let prefix = target_family_prefix ^ "_" in
              if String.sub enum_upper 0 (String.length prefix) = prefix then
                (* Extract instruction name *)
                String.sub enum_upper (String.length prefix) 
                  (String.length enum_upper - String.length prefix)
              else
                enum_upper
            else
              enum_upper
          in
          
          (* Translate execute clause, mapping register reads to local vars *)
          let operand_names = List.map fst operands in
          let operation = translate_execute_for_case constructor_name enum_value_id 
                           execute_clauses operand_names in
          
          (* Replace rf_xpr_read(regname) with local variable name *)
          (* Also replace immediate operand names and their subranges *)
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
          (* Also replace (uint5)shamt or (uint5)imm with immediate *)
          let operation_with_imm = List.fold_left (fun acc (imm_name, local_var) ->
            (* Replace (uint5)imm_name with local_var *)
            let pattern = Printf.sprintf "(uint5)%s" imm_name in
            let rec replace_all s =
              try
                let idx = Str.search_forward (Str.regexp_string pattern) s 0 in
                let before = String.sub s 0 idx in
                let after = String.sub s (idx + String.length pattern) (String.length s - idx - String.length pattern) in
                replace_all (before ^ local_var ^ after)
              with Not_found -> s
            in
            replace_all acc
          ) operation_with_locals imm_var_map in
          
          (* Convert ternary comparisons to if-else statements and ensure result = prefix *)
          (* General approach: find "? 1 : 0" pattern and extract the condition before it *)
          let operation_final = 
            (* First, ensure result = prefix for all expressions *)
            let expr_with_result = 
              if String.length operation_with_imm > 0 && not (Str.string_match (Str.regexp_string "result =") operation_with_imm 0) then
                "result = " ^ operation_with_imm
              else
                operation_with_imm
            in
            
            (* Then, convert ternary operators to if-else for RTYPE/ITYPE *)
            if (constructor_name = "RTYPE" || constructor_name = "ITYPE") then
              (* Find the pattern: anything followed by "? 1 : 0" *)
              (* Use string search to find the ternary operator pattern *)
              let ternary_suffix = " ? 1 : 0" in
              let find_ternary s =
                let len = String.length s in
                let suffix_len = String.length ternary_suffix in
                if len >= suffix_len then
                  let suffix_start = len - suffix_len in
                  if String.sub s suffix_start suffix_len = ternary_suffix then
                    Some (String.sub s 0 suffix_start)
                  else
                    None
                else
                  None
              in
              match find_ternary expr_with_result with
              | Some condition_expr ->
                  (* Extract condition by removing "result = " prefix if present *)
                  let condition = 
                    if Str.string_match (Str.regexp_string "result = ") condition_expr 0 then
                      String.sub condition_expr 9 (String.length condition_expr - 9)
                    else
                      condition_expr
                  in
                  (* Simplify condition: remove extra (uint32) wrapper casts *)
                  (* Pattern: (uint32)((int32)a < (int32)b) -> ((int32)a < (int32)b) *)
                  (* Pattern: (uint32)((uint32)a < (uint32)b) -> (a < b) *)
                  let simplified_condition = 
                    let rec simplify s =
                      (* Remove (uint32) wrapper around comparisons *)
                      let uint32_wrapper = Str.regexp "(uint32)\\(([^)]+)\\)" in
                      if Str.string_match uint32_wrapper s 0 then
                        let inner = Str.matched_group 1 s in
                        (* If inner contains comparison operators, remove outer cast *)
                        if Str.string_match (Str.regexp ".*[<>=!].*") inner 0 then
                          simplify inner
                        else
                          s
                      else
                        (* Also simplify double casts like (int32)(int32)immediate -> (int32)immediate *)
                        let double_int32 = Str.regexp "(int32)\\(int32\\)" in
                        if Str.string_match double_int32 s 0 then
                          simplify (Str.global_replace double_int32 "(int32)" s)
                        else
                          s
                    in
                    simplify condition
                  in
                  Printf.sprintf "if (%s) result = 1;\n                else result = 0;" simplified_condition
              | None ->
                  (* Ensure semicolon at end if not present *)
                  if String.length expr_with_result > 0 && not (Str.string_match (Str.regexp_string ";") expr_with_result (String.length expr_with_result - 1)) then
                    expr_with_result ^ ";"
                  else
                    expr_with_result
            else
              (* For other instruction types, ensure semicolon at end *)
              if String.length expr_with_result > 0 && not (Str.string_match (Str.regexp_string ";") expr_with_result (String.length expr_with_result - 1)) then
                expr_with_result ^ ";"
              else
                expr_with_result
          in
          
          Printf.sprintf "            case %s_%s:\n                %s\n                break;" 
            target_family_prefix op_upper operation_final
        ) enum_values in
        
        let switch_body = String.concat "\n" switch_cases ^ 
          "\n            default:\n                result = 0;\n                break;" in
        
        (* Generate semantics section with local variables *)
        (* Declare local vars for sources + result (+ immediate if needed) *)
        let semantics_vars = 
          if constructor_name = "BTYPE" then
            "        uint32 result, target_address;\n        uint32 " ^ (String.concat ", " src_var_names) ^ ";"
          else if constructor_name = "STORE" then
            "        uint32 address, result;"
          else if constructor_name = "LOAD" then
            "        uint32 address, result;"
          else if constructor_name = "JAL" || constructor_name = "JALR" then
            "        uint32 target_address, current_pc;"
          else if source_regs <> [] then
            "        uint32 " ^ (String.concat ", " src_var_names) ^ ", result;"
          else 
            "        uint32 result;"
        in
        
        (* Generate reads into LOCAL VARIABLES (only source registers, not dest) *)
        let semantics_reads = 
          if constructor_name = "STORE" || constructor_name = "LOAD" then
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
          else if constructor_name = "LOAD" then
            (match (register_ops, immediate_ops) with
             | (rs1 :: rd :: _, simm :: _) ->
                 Printf.sprintf "        codasip_compiler_schedule_class(sc_load);\n\n        address = rf_xpr_read(%s) + (int32) %s;\n        result = load(opc, address);\n        rf_xpr_write(result, %s);" 
                   rs1 (fst simm) rd
             | _ -> "")
          else if constructor_name = "STORE" then
            (match (register_ops, immediate_ops) with
             | (rs2 :: rs1 :: _, simm :: _) ->
                 Printf.sprintf "        address = rf_xpr_read(%s) + (int32) %s;\n        result = rf_xpr_read(%s);\n        store(opc, address, result);" 
                   rs1 (fst simm) rs2
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
        (* For LOAD/STORE, immediate is handled in writes section, so skip here *)
        let (semantics_vars, semantics_reads) = 
          if immediate_ops <> [] && constructor_name <> "STORE" && constructor_name <> "LOAD" && constructor_name <> "JAL" && constructor_name <> "JALR" then
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
        
        (* Replace 'imm' with 'immediate' in switch cases for ITYPE *)
        let switch_body = 
          if constructor_name = "ITYPE" then
            Str.global_replace (Str.regexp_string "imm") "immediate" switch_body
          else switch_body
        in
        
        let semantics = 
          (* For LOAD/STORE, don't use switch statement - semantics are simpler *)
          if constructor_name = "LOAD" || constructor_name = "STORE" then
            let writes_section = if semantics_writes <> "" then "\n" ^ semantics_writes else "" in
            Printf.sprintf "    semantics\n    {\n%s%s\n    };" 
              semantics_vars writes_section
          else
            let reads_section = if semantics_reads <> "" then 
              "\n\n        // read source operands\n        " ^ semantics_reads ^ "\n"
            else "\n" in
            let writes_section = if semantics_writes <> "" then 
              "\n\n        // store result\n" ^ semantics_writes ^ "\n"
            else "\n" in
            Printf.sprintf "    semantics\n    {\n%s%s        switch (opc)\n        {\n%s\n        }%s    };" 
              semantics_vars reads_section switch_body writes_section
        in
        
        (* Generate opc set name - use correct set suffix *)
        let (_, _, set_suffix) = map_family_name_with_suffix constructor_name in
        let opc_set_name = "opc_" ^ set_suffix in
        
        (* Put it all together *)
        (* Get correct element name using mapping *)
        let (_, element_suffix, _) = map_family_name_with_suffix constructor_name in
        Printf.sprintf "element i_%s\n{\n    use %s as opc;\n%s%s\n    %s\n\n    %s\n\n%s\n};"
          element_suffix opc_set_name use_regs use_imms assembly_syntax binary_encoding semantics
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
      
      let map_family_name (constructor_name : string) : string =
        match constructor_name with
        | "JALR" | "LOAD" -> "ITYPE"  (* Merge into ITYPE *)
        | "STORE" -> "STYPE"  (* Rename to STYPE *)
        | "SHIFTIOP" -> "IMM_SHIFT"  (* Rename to IMM_SHIFT *)
        | "JAL" -> "JTYPE"  (* Rename to JTYPE *)
        | _ -> constructor_name  (* Keep as-is *)
      in
      
      (* Group opcodes by mapped family name *)
      let opcodes_by_family = 
        let family_map = List.fold_left (fun acc opc ->
          let original_family = string_of_id opc.oi_constructor in
          let target_family = map_family_name original_family in
          let existing = try List.assoc target_family acc with Not_found -> [] in
          (target_family, opc :: existing) :: (List.remove_assoc target_family acc)
        ) [] extracted_opcodes in
        family_map
      in
      
      let compute_opcode_width (constructor_name : string) : (string * int) =
        (* Try to find encdec pattern for this constructor *)
        match find_encdec_left_pattern (mk_id constructor_name) with
        | Some _left_mpexp ->
            (* Find the corresponding right pattern from encdec clause *)
            let encdec_id = mk_id "encdec" in
            (match IdMap.find_opt encdec_id mapping_info with
             | Some info ->
                 let rec find_right_pattern = function
                   | [] -> None
                   | mapcl :: rest ->
                       match mapcl with
                       | MCL_aux (MCL_bidir (left, right), _) ->
                           (* Check if left matches *)
                           let extract_constructor mpexp =
                             match mpexp with
                             | MPat_aux (MPat_pat (MP_aux (MP_app (id, _), _)), _) -> Some id
                             | MPat_aux (MPat_when (mpat, _), _) ->
                                 (match mpat with
                                  | MP_aux (MP_app (id, _), _) -> Some id
                                  | _ -> None)
                             | _ -> None
                           in
                           (match extract_constructor left with
                            | Some id when Id.compare id (mk_id constructor_name) = 0 ->
                                Some right
                            | _ -> find_right_pattern rest)
                       | _ -> find_right_pattern rest
                 in
                 (match find_right_pattern info.mi_clauses with
                  | Some right_mpexp ->
                      (* Extract pattern parts *)
                      let (_, (func7_opt, func3_opt, opcode_opt)) = 
                        extract_pattern_parts_from_concat right_mpexp
                      in
                      (* Count bits: func7 + func3 + opcode *)
                      let width = 
                        (match func7_opt with
                         | Some _ -> 
                             (* Check if it's 6-bit func7 (SHIFTIOP) or 7-bit *)
                             (* For SHIFTIOP, we pad 6-bit to 7-bit, so count as 7 *)
                             if constructor_name = "SHIFTIOP" || constructor_name = "IMM_SHIFT" then 7
                             else 7
                         | None -> 0) +
                        (match func3_opt with Some _ -> 3 | None -> 0) +
                        (match opcode_opt with Some _ -> 7 | None -> 0)
                      in
                      (* Determine appropriate uint type *)
                      let enum_type = 
                        if width <= 7 then "uint7"
                        else if width <= 10 then "uint10"
                        else if width <= 16 then "uint16"
                        else if width <= 17 then "uint17"
                        else if width <= 32 then "uint32"
                        else "uint64"
                      in
                      (enum_type, width)
                  | None ->
                      failwith (Printf.sprintf "compute_opcode_width: Could not find right pattern for %s" constructor_name))
             | None ->
                 failwith (Printf.sprintf "compute_opcode_width: encdec mapping not found for %s" constructor_name))
        | None ->
            failwith (Printf.sprintf "compute_opcode_width: Could not find encdec left pattern for %s" constructor_name)
      in
      
      (* Generate enum for each family *)
      let generate_enum_for_family (family_name, opcs) =
        if opcs = [] then ""
        else
          let constructor_name = match opcs with
            | opc :: _ -> string_of_id opc.oi_constructor
            | [] -> family_name
          in
          let (enum_type, _enum_width) = compute_opcode_width constructor_name in
          
          (* Map family name to target family for enum name *)
          (* e.g., SHIFTIOP -> IMM_SHIFT, LOAD -> ITYPE, STORE -> STYPE *)
          let (target_family_for_enum, _, _) = map_family_name_with_suffix family_name in
          let target_family_upper = String.uppercase_ascii target_family_for_enum in
          let enum_name = target_family_upper ^ "_OPCODES" in
          let enum_entries = List.map (fun opc ->
            let original_family = string_of_id opc.oi_constructor in
            let op_name = string_of_id opc.oi_enum_value in
            let op_upper = String.uppercase_ascii op_name in
            (* Remove original constructor prefix from enum_value name if it exists *)
            (* For LOAD/STORE, enum_value is already ITYPE_LB/STYPE_SB, so extract LB/SB *)
            (* For others, remove original prefix like SHIFTIOP_SLLI -> SLLI *)
            let clean_op_name = 
              if original_family = "LOAD" || original_family = "STORE" then
                (* Enum value is already ITYPE_LB or STYPE_SB, extract LB/SB *)
                let (target_fam, _, _) = map_family_name_with_suffix original_family in
                let target_prefix = String.uppercase_ascii target_fam ^ "_" in
                if String.length op_upper > String.length target_prefix &&
                   String.sub op_upper 0 (String.length target_prefix) = target_prefix then
                  String.sub op_upper (String.length target_prefix) 
                    (String.length op_upper - String.length target_prefix)
                else
                  op_upper
              else
                (* For other families, remove original prefix *)
                let original_prefix = String.uppercase_ascii original_family ^ "_" in
                if String.length op_upper > String.length original_prefix &&
                   String.sub op_upper 0 (String.length original_prefix) = original_prefix then
                  String.sub op_upper (String.length original_prefix) 
                    (String.length op_upper - String.length original_prefix)
                else
                  op_upper
            in
            (* Special handling for JALR and JAL: use constructor name instead of enum_value *)
            let final_op_name = match original_family with
              | "JALR" -> "JALR"  (* JALR_RD -> JALR *)
              | "JAL" -> "JAL"    (* JAL_RD -> JAL *)
              | _ -> clean_op_name
            in
            (* Use target family name for enum entry prefix *)
            let enum_entry_name = target_family_upper ^ "_" ^ final_op_name in
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
    
    
    (* Define family order to match reference isa.codal *)
    (* Order: RTYPE, IMM_SHIFT (SHIFTIOP), ITYPE (includes LOAD, JALR), STYPE (STORE), UTYPE, JTYPE (JAL), BTYPE *)
    let get_family_priority (constructor_name : string) : int =
      match constructor_name with
      | "RTYPE" -> 1
      | "SHIFTIOP" -> 2  (* Will be renamed to IMM_SHIFT *)
      | "ITYPE" | "LOAD" | "JALR" -> 3  (* All merged/grouped as ITYPE *)
      | "STORE" -> 4  (* Will be renamed to STYPE *)
      | "UTYPE" -> 5
      | "JAL" -> 6  (* Will be renamed to JTYPE *)
      | "BTYPE" -> 7
      | _ -> 99  (* Unknown families go last *)
    in
    
    (* Sort clauses by family priority - shared by generate_isa_set and generate_all_family_blocks *)
    let sorted_ast_clauses = List.sort (fun clause1 clause2 ->
      let name1 = string_of_id clause1.uc_constructor in
      let name2 = string_of_id clause2.uc_constructor in
      let priority1 = get_family_priority name1 in
      let priority2 = get_family_priority name2 in
      compare priority1 priority2
    ) ast_clauses in
    
    (* Generate ISA set from all instruction families in sorted order *)
    (* Use the same sorted order as generate_all_family_blocks *)
    let generate_isa_set () =
      let element_names = List.filter_map (fun clause ->
        let constructor_name = string_of_id clause.uc_constructor in
        let (_, element_suffix, _) = map_family_name_with_suffix constructor_name in
        let enum_values = match extract_enum_type_from_clause clause with
          | Some enum_id ->
              (match IdMap.find_opt enum_id enum_info with
               | Some ids -> if ids <> [] then Some ids else None
               | None -> None)
          | None -> None
        in
        match enum_values with
        | Some _ -> Some ("i_" ^ element_suffix)
        | None -> None
      ) sorted_ast_clauses in
      
      (* Remove duplicates (e.g., ITYPE_ALU and ITYPE_LOADS both exist) *)
      let unique_element_names = 
        let rec remove_dups acc = function
          | [] -> List.rev acc
          | x :: xs -> if List.mem x acc then remove_dups acc xs else remove_dups (x :: acc) xs
        in
        remove_dups [] element_names
      in
      
      if unique_element_names = [] then "set isa = i_rtype_alu;"
      else "set isa = " ^ (String.concat ", " unique_element_names) ^ ";"
    in
    
    (* Generate per-family block: DEF_OPC, set, element together *)
    let generate_family_block (clause : union_clause_info) : string =
      let constructor_name = string_of_id clause.uc_constructor in
      let (target_family, _element_suffix, set_suffix) = map_family_name_with_suffix constructor_name in
      let target_family_upper = String.uppercase_ascii target_family in
      
      (* Get enum values for this family *)
      (* For LOAD/STORE, use extracted_opcodes instead of enum_info *)
      let enum_values = 
        if constructor_name = "LOAD" || constructor_name = "STORE" then
          (* Extract enum values from extracted_opcodes for this constructor *)
          List.filter_map (fun opc ->
            if Id.compare opc.oi_constructor clause.uc_constructor = 0 then
              Some opc.oi_enum_value
            else None
          ) extracted_opcodes
        else
          (* For other instructions, use enum_info as before *)
          match extract_enum_type_from_clause clause with
          | Some enum_id -> (match IdMap.find_opt enum_id enum_info with
              | Some ids -> ids | None -> [])
          | None -> []
      in
      
      if enum_values = [] then "" else
        (* Generate DEF_OPC calls for this family *)
        (* For LOAD/STORE, extract mnemonic from enum_value name (e.g., ITYPE_LB -> lb) *)
        let opc_defs = String.concat "\n" (List.map (fun enum_value_id ->
          let enum_value_name = string_of_id enum_value_id in
          (* Extract mnemonic: for LOAD/STORE, enum_value is like ITYPE_LB -> extract LB and convert to lb *)
          (* For others, try mnemonic mapping first, then fallback to enum name *)
          let mnemonic = 
            if constructor_name = "LOAD" || constructor_name = "STORE" then
              (* Extract instruction name from enum: ITYPE_LB -> lb, STYPE_SB -> sb *)
              let enum_upper = String.uppercase_ascii enum_value_name in
              if String.length enum_upper > String.length target_family_upper + 1 then
                let prefix = target_family_upper ^ "_" in
                if String.sub enum_upper 0 (String.length prefix) = prefix then
                  String.lowercase_ascii (String.sub enum_upper (String.length prefix) 
                    (String.length enum_upper - String.length prefix))
                else
                  String.lowercase_ascii enum_value_name
              else
                String.lowercase_ascii enum_value_name
            else
              (* For other instructions, use mnemonic mapping *)
              match find_mnemonic_for_enum constructor_name enum_value_id with
              | Some m -> m
              | None -> String.lowercase_ascii enum_value_name
          in
          (* For DEF_OPC enum reference, use the enum_value_name as-is if it already has the prefix *)
          (* Otherwise, construct it from target_family + enum name *)
          let enum_ref = 
            let enum_upper = String.uppercase_ascii enum_value_name in
            if String.length enum_upper > String.length target_family_upper + 1 then
              let prefix = target_family_upper ^ "_" in
              if String.sub enum_upper 0 (String.length prefix) = prefix then
                (* Already has correct prefix, use as-is *)
                enum_value_name
              else
                (* Doesn't have prefix, construct it *)
                target_family_upper ^ "_" ^ enum_upper
            else
              (* Too short, construct it *)
              target_family_upper ^ "_" ^ enum_upper
          in
          Printf.sprintf "DEF_OPC(%s, \"%s\", %s)" 
            mnemonic mnemonic enum_ref
        ) enum_values) in
        
        (* Generate set for this family *)
        let opc_names = List.map (fun id -> 
          let enum_name = string_of_id id in
          (* For LOAD/STORE, extract mnemonic from enum name *)
          let opc_name = if constructor_name = "LOAD" || constructor_name = "STORE" then
            let enum_upper = String.uppercase_ascii enum_name in
            if String.length enum_upper > String.length target_family_upper + 1 then
              let prefix = target_family_upper ^ "_" in
              if String.sub enum_upper 0 (String.length prefix) = prefix then
                String.lowercase_ascii (String.sub enum_upper (String.length prefix) 
                  (String.length enum_upper - String.length prefix))
              else
                String.lowercase_ascii enum_name
            else
              String.lowercase_ascii enum_name
          else
            String.lowercase_ascii enum_name
          in
          "opc_" ^ opc_name
        ) enum_values in
        let opc_set = Printf.sprintf "set opc_%s = %s;" set_suffix (String.concat ", " opc_names) in
        
        (* Generate element for this family *)
        (* generate_instruction_element already uses correct element name via map_family_name_with_suffix *)
        let element = generate_instruction_element clause in
        
        (* Combine: comment, DEF_OPC, set, element *)
        Printf.sprintf "// %s Instructions\n\n%s\n\n%s\n\n%s" 
          constructor_name opc_defs opc_set element
    in
    
    (* Generate all family blocks in sorted order *)
    let generate_all_family_blocks () =
      let blocks = List.filter_map (fun clause ->
        let block = generate_family_block clause in
        if block = "" then None else Some block
      ) sorted_ast_clauses in
      String.concat "\n\n" blocks
    in
    
    (* Main codal file content - grouped per family like isa.codal *)
    let main_file_content =
      "/* Generated Codal ISA from Sail AST */\n\n" ^
      "#include \"opcodes.hcodal\"\n" ^
      "#include \"utils.hcodal\"\n" ^
      "#include \"config.hcodal\"\n" ^
      "#include \"debug.hcodal\"\n\n" ^
      "/* Main ISA set */\n" ^
      generate_isa_set () ^ "\n\n" ^
      "/* Start section */\n" ^
      "start\n{\n  roots = { isa };\n};\n\n" ^
      generate_all_family_blocks ()
    in
    
    (* Generate opcodes header *)
    let opcodes_header_content = generate_opcodes_header () in
    
    (* Return tuple (main_content, opcodes_header_content) *)
    (main_file_content, opcodes_header_content)

  let compile_ast _env _effects basename ast _sail_source =
    (* Collect union clauses - instruction families *)
    let union_info = collect_union_clauses ast.defs in
    
    (* Collect enum literals - operation types *)
    let enum_info = collect_enum_literals ast.defs in
    
    (* Collect mappings - encdec bit patterns *)
    let mapping_info = collect_mappings ast.defs in
    
    (* Generate CodAL *)
    let (main_content, opcodes_header_content) = 
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

