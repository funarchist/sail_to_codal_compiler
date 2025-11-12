(** Minimal OCaml skeleton for a Sail-to-CodAL compiler **)

(* src/common/utils.ml *)
let read_file path =
  let ic = open_in path in
  let len = in_channel_length ic in
  let content = really_input_string ic len in
  close_in ic; content

let write_file path content =
  let oc = open_out path in
  output_string oc content;
  close_out oc

let log msg = Printf.printf "[LOG] %s\n%!" msg


(* src/frontend/ast.ml *)
type expr =
  | Var of string
  | Int of int
  | Let of string * expr * expr
  | Call of string * expr list


(* src/frontend/sail_parser.ml *)
open Ast

let parse_sail (_: string) : expr list =
  (* Placeholder: would invoke actual parser *)
  [Let ("x", Int 42, Var "x")]


(* src/frontend/sail_to_ir.ml *)
open Ast

type ir =
  | IR_Let of string * ir * ir
  | IR_Int of int
  | IR_Var of string
  | IR_Call of string * ir list

let rec convert_expr = function
  | Var x -> IR_Var x
  | Int n -> IR_Int n
  | Let (x, e1, e2) -> IR_Let (x, convert_expr e1, convert_expr e2)
  | Call (f, args) -> IR_Call (f, List.map convert_expr args)

let convert (ast: expr list) : ir list =
  List.map convert_expr ast


(* src/middle/ir_transform.ml *)
open Sail_to_ir

let rec simplify_ir = function
  | IR_Let (x, IR_Int n, body) when x = "_" -> simplify_ir body
  | IR_Let (x, e1, e2) -> IR_Let (x, simplify_ir e1, simplify_ir e2)
  | IR_Call (f, args) -> IR_Call (f, List.map simplify_ir args)
  | e -> e

let simplify (irs: ir list) : ir list =
  List.map simplify_ir irs


(* src/backend/cgen_codal.ml *)
open Sail_to_ir

let rec ir_to_codal = function
  | IR_Int n -> string_of_int n
  | IR_Var x -> x
  | IR_Let (x, e1, e2) ->
    "let " ^ x ^ " = " ^ ir_to_codal e1 ^ ";\n" ^ ir_to_codal e2
  | IR_Call (f, args) ->
    f ^ "(" ^ String.concat ", " (List.map ir_to_codal args) ^ ")"

let generate (irs: ir list) : string =
  String.concat "\n" (List.map ir_to_codal irs)


(* src/main.ml *)
open Utils
open Sail_parser
open Sail_to_ir
open Ir_transform
open Cgen_codal
open Sail_codal_backend.Codal_backend

let () =
  let input = "input.sail" in
  let output = "output.codal" in
  let sail_ir =
    let ic = open_in input in
    let rec read_lines acc =
      match input_line ic with
      | line -> read_lines (line :: acc)
      | exception End_of_file -> List.rev acc
    in
    let lines = read_lines [] in
    close_in ic;
    lines
  in
  let codal_lines = translate sail_ir in
  let oc = open_out output in
  List.iter (fun line -> output_string oc (line ^ "\n")) codal_lines;
  close_out oc
