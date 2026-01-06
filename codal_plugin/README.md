# CodAL Plugin - Comprehensive Guide for Beginners

## Table of Contents
1. [Overview](#overview)
2. [What is CodAL?](#what-is-codal)
3. [Architecture Overview](#architecture-overview)
4. [File Structure](#file-structure)
5. [How It Works - Detailed Walkthrough](#how-it-works---detailed-walkthrough)
6. [Key Concepts Explained](#key-concepts-explained)
7. [Building the Plugin](#building-the-plugin)
8. [Using the Plugin](#using-the-plugin)
9. [Input Format (Sail Language)](#input-format-sail-language)
10. [Output Format (CodAL Language)](#output-format-codal-language)
11. [Translation Process Deep Dive](#translation-process-deep-dive)
12. [Examples](#examples)
13. [Troubleshooting](#troubleshooting)
14. [Advanced Topics](#advanced-topics)
15. [Architecture Notes](#architecture-notes)

---

## Overview

The `codal_plugin` is a **Sail compiler backend** that automatically translates Sail instruction set architecture (ISA) descriptions into CodAL (Code Architecture Description Language) format. This plugin enables you to generate CodAL code from Sail specifications, which is particularly useful for RISC-V and other instruction set architectures.

### What Problem Does It Solve?

- **Manual Translation is Error-Prone**: Converting Sail specifications to CodAL manually is tedious, time-consuming, and error-prone
- **Consistency**: Ensures that opcode patterns, semantics, and instruction formats are consistently translated across all instructions
- **Automation**: Automatically extracts instruction encodings, semantics, and mnemonics from Sail AST without manual intervention
- **Maintainability**: When Sail specifications change, CodAL can be regenerated automatically, keeping both in sync
- **Scalability**: Handles large instruction sets (like full RISC-V) efficiently

### Key Features

- ✅ **Direct AST Translation**: Works directly with Sail AST, no intermediate representation
- ✅ **Automatic Opcode Extraction**: Extracts bit patterns from `encdec` mappings
- ✅ **Semantic Translation**: Translates Sail expressions to CodAL automatically
- ✅ **Assembly Syntax Generation**: Generates assembly syntax from Sail mappings
- ✅ **Binary Encoding**: Creates CodAL binary encoding templates
- ✅ **Multiple Instruction Families**: Supports RTYPE, ITYPE, LOAD, STORE, BTYPE, JAL, JALR, etc.

---

## What is CodAL?

**CodAL** (Code Architecture Description Language) is a domain-specific language used to describe instruction set architectures in a format that can be processed by hardware design tools and simulators. CodAL files describe:

- **Instruction encodings**: How instructions are encoded in binary (opcode patterns)
- **Instruction semantics**: What each instruction does (register reads/writes, arithmetic operations, etc.)
- **Assembly syntax**: How instructions are written in assembly language
- **Instruction families**: Groupings of related instructions (e.g., all R-type instructions)

CodAL is used by hardware design tools to:
- Generate instruction decoders
- Create simulators and emulators
- Verify instruction correctness
- Generate documentation

---

## Architecture Overview

The plugin consists of two main components that work together:

```
┌─────────────────────────────────────────────────────────────┐
│                    Sail Compiler                            │
│  (sail --plugin sail_plugin_codal_gold.cmxs --codal ...)   │
│                                                             │
│  1. Parses Sail files (.sail)                              │
│  2. Builds Abstract Syntax Tree (AST)                       │
│  3. Applies rewrites (instantiate_outcomes, recheck_defs)   │
│  4. Calls codal_target function                             │
└──────────────────────┬──────────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────────┐
│         sail_plugin_codal_gold.ml (90 lines)                 │
│  • Registers the "codal" target with Sail                   │
│  • Applies Sail rewrites                                     │
│  • Instantiates Codalgen module                             │
│  • Calls compile_ast                                        │
│  • Writes output files                                       │
└──────────────────────┬──────────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────────┐
│      codal_backend_gold.ml (2601 lines)                     │
│                                                             │
│  Phase 1: COLLECTION                                        │
│  ├─ collect_union_clauses    → Instruction families         │
│  ├─ collect_enum_literals    → Operation types              │
│  ├─ collect_mappings         → encdec/assembly mappings     │
│  └─ collect_execute_clauses  → Semantic definitions         │
│                                                             │
│  Phase 2: TRANSLATION                                       │
│  ├─ parse_encdec_clause      → Extract opcode patterns     │
│  ├─ extract_operand_info     → Identify operands            │
│  ├─ extract_assembly_order   → Assembly syntax order        │
│  ├─ generate_binary_encoding → CodAL binary templates       │
│  └─ translate_exp            → Sail → CodAL expressions     │
│                                                             │
│  Phase 3: CODE GENERATION                                   │
│  ├─ generate_opcodes_header  → opcodes.hcodal              │
│  ├─ generate_instruction_element → Instruction elements     │
│  └─ ast_to_codal             → Main CodAL file             │
└──────────────────────┬──────────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────────┐
│              Generated CodAL Files                          │
│  • <output>.codal      → Main ISA definition                │
│  • opcodes.hcodal      → Opcode constants (C-style enums)   │
└─────────────────────────────────────────────────────────────┘
```

### Design Philosophy

**Important**: This backend does **NOT** use Sail's intermediate representation (JIB). Instead, it works directly with the Sail AST. This is crucial because:

1. **Opcode Patterns**: The `encdec` mappings contain bit patterns that would be lost if converted to functions via `realize_mappings`
2. **Structural Information**: Union clauses and enum types need to be preserved as-is for instruction family detection
3. **Semantic Translation**: Execute function clauses are translated directly from Sail AST expressions to CodAL, preserving the original structure

---

## File Structure

```
codal_plugin/
├── README.md                          # This comprehensive guide
├── BACKEND_ARCHITECTURE.md            # Detailed architecture analysis
├── dune                               # Dune build configuration
├── dune-project                       # Dune project metadata
├── sail_plugin_codal_gold.ml          # Plugin entry point (registers with Sail)
├── codal_backend_gold.ml              # Main backend implementation (2601 lines)
├── compile_riscv_insts_base.sh        # Script to compile full RISC-V base instructions
├── custom_riscv.sail                  # Example Sail input file
├── opcodes.hcodal                     # Generated opcodes header (output)
├── isa_compare.codal                  # Reference CodAL file for comparison
└── _build/                            # Build artifacts (generated)
    └── default/
        ├── sail_plugin_codal_gold.cmxs # Compiled plugin (native)
        └── sail_plugin_codal_gold.cmo  # Compiled plugin (bytecode)
```

### Key Files Explained

#### `sail_plugin_codal_gold.ml` (90 lines)
- **Purpose**: Wires the CodAL backend into Sail's target system
- **Key Functions**:
  - `codal_target`: Main entry point called by Sail compiler
  - Registers the plugin with `Target.register`
- **Rewrites Applied**:
  - `instantiate_outcomes`: Instantiates Sail outcome types
  - `recheck_defs`: Re-checks type definitions
  - **Note**: Does NOT use `realize_mappings` (to preserve opcode patterns)

#### `codal_backend_gold.ml` (2601 lines)
- **Purpose**: Core translation engine
- **Main Module**: `Codalgen` functor that generates CodAL code
- **Key Functions**:
  - `compile_ast`: Main compilation function (entry point)
  - `ast_to_codal`: Generates CodAL from AST
  - `translate_exp`: Translates Sail expressions to CodAL
  - `collect_union_clauses`: Extracts instruction families
  - `collect_mappings`: Extracts encdec mappings
  - `collect_execute_clauses`: Extracts semantic definitions
  - `generate_instruction_element`: Generates complete instruction elements
  - `generate_assembly_syntax`: Generates assembly syntax
  - `generate_binary_encoding`: Generates binary encoding templates

#### `BACKEND_ARCHITECTURE.md` (294 lines)
- **Purpose**: Detailed analysis of backend architecture and generality
- **Contents**:
  - Phase-by-phase breakdown
  - Generality assessment (what works for any ISA vs. RISC-V specific)
  - Portability analysis
  - Recommendations for generalization

#### `compile_riscv_insts_base.sh` (86 lines)
- **Purpose**: Example script to compile full RISC-V base instructions
- **What it does**:
  1. Builds the plugin
  2. Navigates to sail-riscv model directory
  3. Compiles all RISC-V base instruction files in correct order
  4. Includes `custom_riscv.sail` for custom instructions
  5. Generates CodAL output

---

## How It Works - Detailed Walkthrough

### Step 1: Sail Compiler Invocation

When you run:
```bash
sail --plugin _build/default/sail_plugin_codal_gold.cmxs --codal input.sail -o output
```

**What happens:**
1. Sail compiler loads the plugin (`sail_plugin_codal_gold.cmxs`)
2. Sail parses `input.sail` and all included files (via `$include`)
3. Sail builds an Abstract Syntax Tree (AST) from the Sail code
4. Sail applies rewrites specified in `codal_rewrites`:
   - `instantiate_outcomes`: Instantiates Sail outcome types
   - `recheck_defs`: Re-checks type definitions
5. Sail calls `codal_target` function with the processed AST

### Step 2: AST Collection Phase

The backend collects structural information from the AST:

```ocaml
(* Collect union clauses - instruction families *)
let union_info = collect_union_clauses ast.defs

(* Collect enum literals - operation types *)
let enum_info = collect_enum_literals ast.defs

(* Collect mappings - encdec bit patterns *)
let mapping_info = collect_mappings ast.defs
```

**What gets collected:**

#### 2.1 Union Clauses (`union clause ast = RTYPE : ...`)
- **Purpose**: Represents instruction families
- **Example**: `union clause ast = RTYPE : (regidx, regidx, regidx, rop)`
- **What it means**:
  - There's an instruction family called `RTYPE`
  - Each RTYPE instruction has 4 arguments:
    - `regidx`: Source register 2 (rs2)
    - `regidx`: Source register 1 (rs1)
    - `regidx`: Destination register (rd)
    - `rop`: Operation type (enum: ADD, SUB, AND, etc.)
- **Output**: Map from union type ID → list of union clause info

#### 2.2 Enum Literals (`enum rop = { ADD, SUB, AND, ... }`)
- **Purpose**: Represents operation types within families
- **Example**: `enum rop = { ADD, SUB, AND, OR, XOR, SLT, SLTU }`
- **What it means**: These are the possible operations for R-type instructions
- **Output**: Map from enum type ID → list of enum member IDs

#### 2.3 Mapping Definitions (`mapping clause encdec = ...`)
- **Purpose**: Contains opcode bit patterns
- **Example**:
  ```sail
  mapping clause encdec = RTYPE(rs2, rs1, rd, ADD)
    <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011
  ```
- **What it means**: This is how ADD instruction is encoded in binary
- **Output**: Map from mapping ID → mapping info (clauses)

#### 2.4 Execute Clauses (`function clause execute(...) = { ... }`)
- **Purpose**: Contains semantic definitions
- **Example**:
  ```sail
  function clause execute (RTYPE(rs2, rs1, rd, ADD)) = {
    X(rd) = X(rs1) + X(rs2);
    RETIRE_SUCCESS
  }
  ```
- **What it means**: This is what ADD instruction does
- **Output**: List of (function_id, pexp) pairs

### Step 3: Translation Phase

For each instruction family, the backend:

#### 3.1 Opcode Extraction (`parse_encdec_clause`)
- **Purpose**: Extract opcode bit patterns from `encdec` mappings
- **Process**:
  1. Finds `encdec` mapping in collected mappings
  2. Parses right-hand side patterns (bit concatenations)
  3. Extracts `func7`, `func3`, `opcode` fields
  4. Computes full opcode values
- **Example**:
  - Input: `0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011`
  - Output: `RTYPE_ADD = 0b00000000000110011`

#### 3.2 Operand Extraction (`extract_operand_info_from_clause`)
- **Purpose**: Identify instruction operands (registers, immediates, enums)
- **Process**:
  1. Extracts variable names from `encdec` left patterns
  2. Matches names with types from union clause arguments
  3. Classifies as Register, Immediate, Enum, or Other
  4. Infers immediate bit widths and signedness
- **Example**:
  - Input: `RTYPE(rs2, rs1, rd, ADD)` with types `[regidx, regidx, regidx, rop]`
  - Output: `[{op_name="rs2", op_type=Register}, {op_name="rs1", op_type=Register}, {op_name="rd", op_type=Register}, {op_name="ADD", op_type=Enum}]`

#### 3.3 Assembly Syntax Extraction (`extract_assembly_order`)
- **Purpose**: Determine operand order in assembly syntax
- **Process**:
  1. Finds `assembly` mapping clause
  2. Parses right-hand side expression/pattern
  3. Extracts `reg_name(...)` calls to determine order
  4. Falls back to left pattern order if parsing fails
- **Example**:
  - Input: `rtype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)`
  - Output: Order is `[rd, rs1, rs2]`

#### 3.4 Binary Encoding Generation (`generate_binary_encoding_template`)
- **Purpose**: Generate CodAL binary encoding strings
- **Process**:
  1. Parses `encdec` right-hand side `MP_vector_concat`
  2. Identifies bit literals, `encdec_reg` calls, immediates
  3. Generates CodAL bitfield macros (`FUNC7`, `FUNC3`, `OPCODE`)
  4. Handles immediate splitting (STORE, BTYPE, JAL)
- **Example**:
  - Input: `0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011`
  - Output: `FUNC7(opc) @ rs2[4..0] @ rs1[4..0] @ FUNC3(opc) @ rd[4..0] @ OPCODE(opc)`

#### 3.5 Semantic Translation (`translate_exp`)
- **Purpose**: Translate Sail expressions to CodAL
- **Process**:
  1. Pattern matches Sail AST expression nodes
  2. Maps Sail functions to CodAL operators:
     - `add_bits` → `+`
     - `sub_vec` → `-`
     - `xor_vec` → `^`
     - `shift_bits_left` → `<<`
     - etc.
  3. Handles type casts, comparisons, extensions
- **Example**:
  - Input: `X(rs1) + X(rs2)`
  - Output: `rf_xpr_read(rs1) + rf_xpr_read(rs2)`

### Step 4: Code Generation Phase

The backend generates CodAL code:

#### 4.1 Opcode Header Generation (`generate_opcodes_header`)
- **Purpose**: Generate `opcodes.hcodal` with enum definitions
- **Process**:
  1. Groups opcodes by instruction family
  2. Computes enum width dynamically
  3. Generates enum type and values
- **Output**: C-style enum definitions

#### 4.2 Instruction Element Generation (`generate_instruction_element`)
- **Purpose**: Generate CodAL `element` blocks for instructions
- **Process**:
  1. Generates `use` declarations (registers, immediates)
  2. Generates assembly syntax
  3. Generates binary encoding
  4. Generates semantics (switch statement with cases)
- **Output**: Complete CodAL instruction element

#### 4.3 Main File Generation (`ast_to_codal`)
- **Purpose**: Generate main CodAL file
- **Process**:
  1. Generates includes (`opcodes.hcodal`, `utils.hcodal`, etc.)
  2. Generates ISA set definition
  3. Generates start section
  4. Generates all instruction family blocks
- **Output**: Complete CodAL ISA file

---

## Key Concepts Explained

### 1. Sail AST (Abstract Syntax Tree)

The Sail compiler parses your `.sail` file into a tree structure called an AST. Each node represents a language construct:

- **`DEF_aux`**: Top-level definition wrapper
- **`DEF_type`**: Type definition (union, enum, etc.)
- **`DEF_fundef`**: Function definition
- **`DEF_mapdef`**: Mapping definition
- **`E_aux`**: Expression node
- **`Pat_aux`**: Pattern node
- **`MPat_aux`**: Mapping pattern node

The backend traverses this AST to extract information. It's like reading a structured document where each node has a specific meaning.

### 2. Union Clauses

In Sail, union clauses define instruction families:

```sail
union clause ast = RTYPE : (regidx, regidx, regidx, rop)
```

**Breaking it down:**
- `union clause ast`: Defines a variant of the `ast` union type
- `RTYPE`: Constructor name (instruction family name)
- `(regidx, regidx, regidx, rop)`: Argument types
  - First `regidx`: Source register 2 (rs2)
  - Second `regidx`: Source register 1 (rs1)
  - Third `regidx`: Destination register (rd)
  - `rop`: Operation type (enum: ADD, SUB, etc.)

**Why it matters:** The backend uses this to understand:
- What instruction families exist
- What operands each family has
- How to group related instructions

### 3. Encdec Mappings

Encdec mappings define how instructions are encoded in binary:

```sail
mapping clause encdec = RTYPE(rs2, rs1, rd, ADD) 
  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011
```

**Breaking it down:**
- `mapping clause encdec`: Defines an encoding/decoding mapping
- `RTYPE(rs2, rs1, rd, ADD)`: Left side (instruction pattern)
- `<->`: Bidirectional mapping
- `0b0000000 @ ... @ 0b0110011`: Right side (bit pattern)
  - `@`: Bit concatenation operator
  - `encdec_reg(rs2)`: Encodes register rs2 as 5 bits
  - `0b0110011`: Opcode (7 bits)

**RISC-V R-type format:**
```
[31:25] func7  (7 bits)
[24:20] rs2    (5 bits)
[19:15] rs1    (5 bits)
[14:12] func3  (3 bits)
[11:7]  rd     (5 bits)
[6:0]   opcode (7 bits)
```

**Why it matters:** The backend extracts these bit patterns to generate:
- Opcode constants (`opcodes.hcodal`)
- Binary encoding templates (CodAL `binary` sections)

### 4. Execute Clauses

Execute clauses define what each instruction does:

```sail
function clause execute (RTYPE(rs2, rs1, rd, op)) = {
  X(rd) = match op {
    ADD => X(rs1) + X(rs2),
    SUB => X(rs1) - X(rs2),
    ...
  };
  RETIRE_SUCCESS
}
```

**Breaking it down:**
- `function clause execute`: Defines execution semantics
- `RTYPE(rs2, rs1, rd, op)`: Pattern matches instruction
- `X(rd) = ...`: Write to destination register
- `X(rs1)`, `X(rs2)`: Read from source registers
- `match op { ... }`: Switch on operation type
- `RETIRE_SUCCESS`: Return success outcome

**Why it matters:** The backend translates these to CodAL semantic sections:
```codal
semantic {
    switch (op) {
        case ADD: rf_xpr_write(rd, rf_xpr_read(rs1) + rf_xpr_read(rs2)); break;
        case SUB: rf_xpr_write(rd, rf_xpr_read(rs1) - rf_xpr_read(rs2)); break;
        ...
    }
}
```

### 5. Expression Translation

The backend translates Sail expressions to CodAL:

| Sail Expression | CodAL Translation | Explanation |
|----------------|-------------------|-------------|
| `X(rs1)` | `rf_xpr_read(rs1)` | Read from register file |
| `X(rd) = value` | `rf_xpr_write(rd, value)` | Write to register file |
| `X(rs1) + X(rs2)` | `rf_xpr_read(rs1) + rf_xpr_read(rs2)` | Addition |
| `X(rs1) & X(rs2)` | `rf_xpr_read(rs1) & rf_xpr_read(rs2)` | Bitwise AND |
| `sign_extend(imm)` | `(int32)imm` | Sign extension |
| `zero_extend(imm)` | `(uint32)imm` | Zero extension |
| `bool_to_bits(cond)` | `(cond) ? 1 : 0` | Boolean to bits |
| `X(rs1) <_s X(rs2)` | `(int32)rf_xpr_read(rs1) < (int32)rf_xpr_read(rs2)` | Signed comparison |
| `shift_bits_left(X(rs1), shamt)` | `rf_xpr_read(rs1) << shamt` | Left shift |

### 6. Operand Information

The backend extracts detailed operand information:

```ocaml
type operand_info = {
  op_name : string;           (* Variable name: rs1, rs2, rd, imm *)
  op_type : operand_type;     (* Register, Immediate, Enum, Other *)
  op_typ : typ;              (* Full Sail type *)
  op_position : int;          (* Position in constructor args *)
  op_bit_width : int option;  (* For immediates: bits(12) -> Some 12 *)
  op_signed : bool option;    (* For immediates: Some true/false or None *)
}
```

**Why it matters:** This information is used to:
- Generate `use` declarations
- Determine register ordering
- Generate assembly syntax
- Generate binary encoding templates

---

## Building the Plugin

### Prerequisites

- **OCaml**: Version 4.12 or later
- **Dune**: Build system for OCaml (usually installed with OCaml)
- **Sail**: Sail compiler installed and in PATH
- **libsail**: Sail library (usually comes with Sail installation)

### Build Steps

1. **Navigate to the plugin directory**:
   ```bash
   cd codal_plugin
   ```

2. **Build the plugin**:
   ```bash
   dune build sail_plugin_codal_gold.cmxs
   ```

   This creates:
   - `_build/default/sail_plugin_codal_gold.cmxs` (native plugin - faster)
   - `_build/default/sail_plugin_codal_gold.cmo` (bytecode plugin - slower but more portable)

3. **Verify the build**:
   ```bash
   ls -lh _build/default/sail_plugin_codal_gold.cmxs
   ```

   You should see a file that's several hundred KB in size.

### Build Configuration

The `dune` file specifies:
```dune
(executable
 (name sail_plugin_codal_gold)
 (modules sail_plugin_codal_gold codal_backend_gold)
 (modes (native plugin) (byte plugin))
 (libraries libsail))
```

**Explanation:**
- **`modes (native plugin)`**: Builds native code plugin (`.cmxs`) - faster execution
- **`modes (byte plugin)`**: Builds bytecode plugin (`.cmo`) - more portable
- **`libraries libsail`**: Links against Sail library (provides AST types, utilities)

### Troubleshooting Build Issues

**Problem**: `dune: command not found`
- **Solution**: Install Dune: `opam install dune`

**Problem**: `Error: Library "libsail" not found`
- **Solution**: Install Sail and ensure `libsail` is in your OCaml path

**Problem**: Type errors during compilation
- **Solution**: Check Sail version compatibility. The backend may need updates for newer Sail versions.

---

## Using the Plugin

### Basic Usage

```bash
sail --plugin _build/default/sail_plugin_codal_gold.cmxs \
     --codal input.sail \
     -o output
```

This generates:
- `output.codal`: Main CodAL file
- `opcodes.hcodal`: Opcodes header (in codal_plugin directory)

### Example: Compiling Custom RISC-V Instructions

```bash
cd codal_plugin
dune build
sail --plugin _build/default/sail_plugin_codal_gold.cmxs \
     --codal custom_riscv.sail \
     -o custom
```

### Example: Compiling Full RISC-V Base Instructions

Use the provided script:
```bash
cd codal_plugin
./compile_riscv_insts_base.sh
```

This script:
1. Builds the plugin
2. Navigates to sail-riscv model directory
3. Compiles all RISC-V base instruction files in correct order
4. Includes `custom_riscv.sail` for custom instructions
5. Generates CodAL output

**Note**: The script assumes `sail-riscv` is in the parent directory. Adjust paths if needed.

### Command-Line Options

- **`--plugin <path>`**: Path to compiled plugin (`.cmxs` file)
  - Required: Yes
  - Example: `--plugin _build/default/sail_plugin_codal_gold.cmxs`

- **`--codal`**: Enables CodAL backend (required)
  - Required: Yes
  - No arguments needed

- **`-o <output>`**: Output file basename (without extension)
  - Required: No (defaults to input filename)
  - Example: `-o riscv_isa`

- **Input files**: One or more `.sail` files to compile
  - Required: Yes
  - Example: `input.sail` or `file1.sail file2.sail`

### Output Files

The plugin generates:

1. **`<output>.codal`**: Main CodAL ISA definition file
   - Contains instruction elements grouped by family
   - Includes opcode definitions, sets, and semantic blocks
   - Location: Current directory

2. **`opcodes.hcodal`**: Opcodes header file
   - Contains C-style enum definitions for opcodes
   - Organized by instruction family
   - Location: `codal_plugin/` directory (or found via path search)

---

## Input Format (Sail Language)

### Basic Structure

A typical Sail file for CodAL generation contains:

1. **Includes**:
   ```sail
   $include <prelude.sail>
   $include "riscv_types_minimal.sail"
   ```

2. **Type Definitions**:
   ```sail
   enum rop = { ADD, SUB, AND, OR, XOR, SLT, SLTU }
   ```

3. **Union Clauses** (Instruction Families):
   ```sail
   union clause ast = RTYPE : (regidx, regidx, regidx, rop)
   ```

4. **Encdec Mappings** (Opcode Patterns):
   ```sail
   mapping clause encdec = RTYPE(rs2, rs1, rd, ADD)
     <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011
   ```

5. **Execute Clauses** (Semantics):
   ```sail
   function clause execute (RTYPE(rs2, rs1, rd, op)) = {
     X(rd) = match op {
       ADD => X(rs1) + X(rs2),
       SUB => X(rs1) - X(rs2),
       ...
     };
     RETIRE_SUCCESS
   }
   ```

6. **Mnemonic Mappings** (Optional):
   ```sail
   mapping rtype_mnemonic : rop <-> string = {
     ADD <-> "add",
     SUB <-> "sub",
     ...
   }
   ```

7. **Assembly Mappings** (Optional):
   ```sail
   mapping clause assembly = RTYPE(rs2, rs1, rd, op)
     <-> rtype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
   ```

### Example: Complete Instruction Definition

```sail
// 1. Define operation enum
enum rop = { ADD, SUB, AND, OR, XOR }

// 2. Define instruction family
union clause ast = RTYPE : (regidx, regidx, regidx, rop)

// 3. Define opcode patterns
mapping clause encdec = RTYPE(rs2, rs1, rd, ADD)
  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011

mapping clause encdec = RTYPE(rs2, rs1, rd, SUB)
  <-> 0b0100000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011

// 4. Define semantics
function clause execute (RTYPE(rs2, rs1, rd, op)) = {
  X(rd) = match op {
    ADD => X(rs1) + X(rs2),
    SUB => X(rs1) - X(rs2),
    AND => X(rs1) & X(rs2),
    OR  => X(rs1) | X(rs2),
    XOR => X(rs1) ^ X(rs2)
  };
  RETIRE_SUCCESS
}

// 5. Define mnemonics (optional)
mapping rtype_mnemonic : rop <-> string = {
  ADD <-> "add",
  SUB <-> "sub",
  AND <-> "and",
  OR  <-> "or",
  XOR <-> "xor"
}

// 6. Define assembly syntax (optional)
mapping clause assembly = RTYPE(rs2, rs1, rd, op)
  <-> rtype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
```

### Example: I-Type Instruction with Immediate

```sail
enum iop = { ADDI, ANDI, ORI, XORI }
union clause ast = ITYPE : (bits(12), regidx, regidx, iop)

mapping clause encdec = ITYPE(imm, rs1, rd, ADDI)
  <-> imm @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0010011

function clause execute (ITYPE(imm, rs1, rd, ADDI)) = {
  let immext : xlenbits = sign_extend(imm);
  X(rd) = X(rs1) + immext;
  RETIRE_SUCCESS
}
```

---

## Output Format (CodAL Language)

### Main CodAL File (`<output>.codal`)

```codal
/* Generated Codal ISA from Sail AST */

#include "opcodes.hcodal"
#include "utils.hcodal"
#include "config.hcodal"
#include "debug.hcodal"

/* Main ISA set */
set isa = i_rtype_alu;

/* Start section */
start
{
  roots = { isa };
};

// RTYPE Instructions

DEF_OPC(add, "add", RTYPE_ADD)
DEF_OPC(sub, "sub", RTYPE_SUB)
DEF_OPC(and, "and", RTYPE_AND)
DEF_OPC(or, "or", RTYPE_OR)
DEF_OPC(xor, "xor", RTYPE_XOR)

set opc_rtype = opc_add, opc_sub, opc_and, opc_or, opc_xor;

element i_rtype_alu
{
    use xpr_all as src1, src2;
    use xpr_all as dest;
    
    assembly {
        switch (op) {
            case ADD: "add" ^ spc() ^ reg_name(dest) ^ sep() ^ reg_name(src1) ^ sep() ^ reg_name(src2);
            case SUB: "sub" ^ spc() ^ reg_name(dest) ^ sep() ^ reg_name(src1) ^ sep() ^ reg_name(src2);
            ...
        }
    };
    
    binary {
        FUNC7(opc) @ src2[4..0] @ src1[4..0] @ FUNC3(opc) @ dest[4..0] @ OPCODE(opc)
    };
    
    semantic {
        uint32 src1_val = rf_xpr_read(src1);
        uint32 src2_val = rf_xpr_read(src2);
        
        switch (op) {
            case ADD:
                rf_xpr_write(dest, src1_val + src2_val);
                break;
            case SUB:
                rf_xpr_write(dest, src1_val - src2_val);
                break;
            ...
        }
    };
}
```

### Opcodes Header (`opcodes.hcodal`)

```c
/**
 * Generated opcodes header from Sail AST
 */

#ifndef OPCODES_HCODAL_HG
#define OPCODES_HCODAL_HG

// RTYPE Opcodes
enum RTYPE_OPCODES : uint17 {
    RTYPE_ADD = 0b00000000000110011,
    RTYPE_SUB = 0b01000000000110011,
    RTYPE_AND = 0b00000001110110011,
    RTYPE_OR  = 0b00000001100110011,
    RTYPE_XOR = 0b00000001000110011
};

#endif
```

**Explanation:**
- **Enum width**: `uint17` means 17-bit unsigned integer (enough for RISC-V 32-bit opcodes)
- **Opcode values**: Computed from `encdec` mappings
- **Family grouping**: Opcodes grouped by instruction family

---

## Translation Process Deep Dive

### 1. Opcode Extraction

**Input (Sail)**:
```sail
mapping clause encdec = RTYPE(rs2, rs1, rd, ADD)
  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011
```

**Process**:
1. Parses the mapping clause
2. Extracts bit pattern: `0b0000000 @ ... @ 0b0110011`
3. Resolves `encdec_reg()` calls (assumes 5-bit register encoding)
4. Computes full opcode value:
   - func7: `0b0000000` (7 bits)
   - rs2: `0b00000` (5 bits, placeholder)
   - rs1: `0b00000` (5 bits, placeholder)
   - func3: `0b000` (3 bits)
   - rd: `0b00000` (5 bits, placeholder)
   - opcode: `0b0110011` (7 bits)
   - Full: `0b00000000000110011` (17 bits)

**Output (CodAL)**:
```c
enum RTYPE_OPCODES : uint17 {
    RTYPE_ADD = 0b00000000000110011
};
```

### 2. Semantic Translation

**Input (Sail)**:
```sail
function clause execute (RTYPE(rs2, rs1, rd, ADD)) = {
  X(rd) = X(rs1) + X(rs2);
  RETIRE_SUCCESS
}
```

**Process**:
1. Parses execute clause pattern: `RTYPE(rs2, rs1, rd, ADD)`
2. Extracts body expression: `X(rd) = X(rs1) + X(rs2)`
3. Translates expressions:
   - `X(rs1)` → `rf_xpr_read(src1)` (where `src1` maps to `rs1`)
   - `X(rs2)` → `rf_xpr_read(src2)` (where `src2` maps to `rs2`)
   - `X(rd) = ...` → `rf_xpr_write(dest, ...)` (where `dest` maps to `rd`)
   - `+` → `+` (preserved)

**Output (CodAL)**:
```codal
semantic {
    uint32 src1_val = rf_xpr_read(src1);
    uint32 src2_val = rf_xpr_read(src2);
    rf_xpr_write(dest, src1_val + src2_val);
}
```

### 3. Instruction Element Generation

For each instruction family, the backend generates:

1. **Use declarations**:
   ```codal
   use xpr_all as src1, src2;
   use xpr_all as dest;
   ```
   - Generated from operand information
   - Groups registers by source/destination

2. **Assembly syntax**:
   ```codal
   assembly {
       switch (op) {
           case ADD: "add" ^ spc() ^ reg_name(dest) ^ sep() ^ reg_name(src1) ^ sep() ^ reg_name(src2);
           ...
       }
   }
   ```
   - Generated from `assembly` mapping or inferred from pattern
   - Uses switch statement for multiple operations

3. **Binary encoding**:
   ```codal
   binary {
       FUNC7(opc) @ src2[4..0] @ src1[4..0] @ FUNC3(opc) @ dest[4..0] @ OPCODE(opc)
   }
   ```
   - Generated from `encdec` mapping
   - Uses CodAL bitfield macros

4. **Semantics**:
   ```codal
   semantic {
       uint32 src1_val = rf_xpr_read(src1);
       uint32 src2_val = rf_xpr_read(src2);
       switch (op) {
           case ADD: rf_xpr_write(dest, src1_val + src2_val); break;
           ...
       }
   }
   ```
   - Generated from `execute` clauses
   - Uses local variables for readability
   - Translates Sail expressions to CodAL

---

## Examples

### Example 1: Simple R-Type Instruction

**Input (`simple_rtype.sail`)**:
```sail
$include <prelude.sail>

enum rop = { ADD, SUB }
union clause ast = RTYPE : (regidx, regidx, regidx, rop)

mapping clause encdec = RTYPE(rs2, rs1, rd, ADD)
  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011

function clause execute (RTYPE(rs2, rs1, rd, ADD)) = {
  X(rd) = X(rs1) + X(rs2);
  RETIRE_SUCCESS
}
```

**Compile**:
```bash
sail --plugin _build/default/sail_plugin_codal_gold.cmxs \
     --codal simple_rtype.sail -o simple
```

**Output (`simple.codal`)**:
```codal
#include "opcodes.hcodal"
#include "utils.hcodal"
#include "config.hcodal"
#include "debug.hcodal"

set isa = i_rtype_alu;

start { roots = { isa }; };

DEF_OPC(add, "add", RTYPE_ADD)

set opc_rtype = opc_add;

element i_rtype_alu {
    use xpr_all as src1, src2;
    use xpr_all as dest;
    
    assembly {
        "add" ^ spc() ^ reg_name(dest) ^ sep() ^ reg_name(src1) ^ sep() ^ reg_name(src2)
    };
    
    binary {
        FUNC7(opc) @ src2[4..0] @ src1[4..0] @ FUNC3(opc) @ dest[4..0] @ OPCODE(opc)
    };
    
    semantic {
        uint32 src1_val = rf_xpr_read(src1);
        uint32 src2_val = rf_xpr_read(src2);
        rf_xpr_write(dest, src1_val + src2_val);
    };
}
```

### Example 2: I-Type Instruction with Immediate

**Input (`itype_example.sail`)**:
```sail
$include <prelude.sail>

enum iop = { ADDI, ANDI }
union clause ast = ITYPE : (bits(12), regidx, regidx, iop)

mapping clause encdec = ITYPE(imm, rs1, rd, ADDI)
  <-> imm @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0010011

function clause execute (ITYPE(imm, rs1, rd, ADDI)) = {
  let immext : xlenbits = sign_extend(imm);
  X(rd) = X(rs1) + immext;
  RETIRE_SUCCESS
}
```

**Output (semantic section)**:
```codal
semantic {
    int32 immediate = (int32)imm;
    uint32 src1_val = rf_xpr_read(src1);
    rf_xpr_write(dest, src1_val + immediate);
}
```

---

## Troubleshooting

### Problem: Plugin Not Found

**Error**:
```
Error: Cannot find plugin file: sail_plugin_codal_gold.cmxs
```

**Solution**:
1. Make sure you've built the plugin: `dune build`
2. Use the correct path: `_build/default/sail_plugin_codal_gold.cmxs`
3. Use absolute path if relative path doesn't work
4. Check that you're in the correct directory

### Problem: Type Errors During Compilation

**Error**:
```
Error: This pattern matches values of type 'a * 'b * 'c
       but a pattern was expected which matches values of type ...
```

**Solution**:
- This usually indicates a mismatch between Sail AST structure and backend expectations
- Check Sail version compatibility
- Review `codal_backend_gold.ml` for AST node handling
- May need to update backend for newer Sail versions

### Problem: Missing Output Files

**Symptom**: Compilation succeeds but no `.codal` files are generated

**Solution**:
1. Check that `--codal` flag is present
2. Verify output directory permissions
3. Check for errors in Sail compilation (may fail silently)
4. Look for error messages in terminal output

### Problem: Incorrect Semantic Translation

**Symptom**: Generated CodAL semantics don't match Sail semantics

**Solution**:
1. Check `translate_exp` function in `codal_backend_gold.ml`
2. Verify Sail expression patterns are handled
3. Add missing expression translations if needed
4. Check operand ordering (rs1 vs rs2)

### Problem: Opcode Patterns Not Extracted

**Symptom**: `opcodes.hcodal` is empty or missing opcodes

**Solution**:
1. Verify `encdec` mappings are present in Sail file
2. Check mapping clause syntax
3. Ensure `realize_mappings` rewrite is NOT applied (it destroys patterns)
4. Check that mapping uses correct constructor name

### Problem: Register Ordering Issues

**Symptom**: Assembly syntax has registers in wrong order

**Solution**:
1. Check `assembly` mapping in Sail file
2. Verify operand extraction is correct
3. Check register ordering logic in `generate_assembly_syntax`
4. Some instruction types (RTYPE, BTYPE) reverse register order

### Problem: Build Errors

**Error**: `dune: command not found`

**Solution**:
```bash
opam install dune
```

**Error**: `Library "libsail" not found`

**Solution**:
1. Install Sail compiler
2. Ensure `libsail` is in OCaml path
3. Check `opam` package installation

---

## Advanced Topics

### Custom Expression Translation

To add support for new Sail expressions, modify `translate_exp` in `codal_backend_gold.ml`:

```ocaml
let rec translate_exp (exp : 'a exp) (var_map : (string * string) list) : string =
  let E_aux (exp_aux, _) = exp in
  match exp_aux with
  | E_app (func_id, args) ->
      let func_name = string_of_id func_id in
      (match func_name with
       | "your_new_function" ->
           (* Add your translation here *)
           Printf.sprintf "codal_equivalent(%s)" 
             (String.concat ", " (List.map (fun a -> translate_exp a var_map) args))
       | _ -> ...)
  | ...
```

### Custom Output Format

To modify output format, edit `ast_to_codal` function:

```ocaml
let ast_to_codal union_info enum_info mapping_info defs =
  (* Modify code generation here *)
  let main_content = 
    "/* Your custom header */\n" ^
    generate_isa_set () ^ "\n" ^
    generate_all_family_blocks ()
  in
  (main_content, opcodes_header_content)
```

### Adding New Instruction Families

The backend automatically detects new instruction families from union clauses:

```sail
union clause ast = NEWTYPE : (regidx, bits(20))
```

Just add:
- Encdec mappings for NEWTYPE
- Execute clauses for NEWTYPE
- The backend will generate CodAL automatically

**Note**: Some instruction families have hardcoded handling (RTYPE, ITYPE, LOAD, STORE, BTYPE, JAL, JALR). New families may need backend updates for:
- Register ordering
- Binary encoding templates
- Semantic generation patterns

### Debugging AST Structure

To debug what the backend sees, add print statements:

```ocaml
let collect_union_clauses defs =
  let handle_def acc = function
    | DEF_aux (DEF_type (TD_aux (TD_variant (union_id, _, clauses, _), _)), _) ->
        Printf.eprintf "Found union: %s\n" (string_of_id union_id);
        (* ... rest of code ... *)
```

### Performance Optimization

For large Sail files:
1. The backend processes all definitions in memory
2. Consider splitting large files into modules
3. Use Sail's `$include` mechanism for code reuse
4. The backend is single-threaded; parallelization would require significant changes

---

## Architecture Notes

### Generality Assessment

The backend is **~60% general** according to `BACKEND_ARCHITECTURE.md`:

- ✅ **Fully General** (Works with any Sail ISA):
  - AST collection functions
  - Pattern extraction
  - Dynamic width computation

- ⚠️ **Partially General** (Works with similar ISAs):
  - Type name assumptions (`regidx`, `bits(N)`)
  - Bit width assumptions (7-bit func7, 3-bit func3, 7-bit opcode)
  - Function name mappings

- ❌ **RISC-V Specific** (Hardcoded):
  - Instruction family names (RTYPE, ITYPE, LOAD, STORE, etc.)
  - Register ordering logic
  - Semantic generation patterns
  - Immediate splitting (STORE, BTYPE, JAL)

### Portability to Other ISAs

**What Would Work Automatically:**
- ✅ ARM: If it uses similar union/enum/mapping structure
- ✅ MIPS: If it uses similar patterns
- ⚠️ x86: Would need significant adaptation

**What Would Need Changes:**
1. **Instruction Family Names** (High Priority)
   - Current: Hardcoded RISC-V names
   - Needed: Dynamic detection or configuration

2. **Register Ordering** (High Priority)
   - Current: Hardcoded per instruction type
   - Needed: Extract from assembly mapping or configuration

3. **Semantic Patterns** (Medium Priority)
   - Current: RISC-V-specific patterns
   - Needed: More generic semantic translation

4. **Bit Width Assumptions** (Medium Priority)
   - Current: Assumes 7/3/7 bit fields
   - Needed: Dynamic detection from patterns

### Current Architecture Strengths

1. **Direct AST Translation**: No intermediate representation
2. **Pattern-Based Extraction**: Works with Sail's structural patterns
3. **Dynamic Width Computation**: Computes opcode widths from patterns
4. **Modular Design**: Separate collection, translation, generation phases

### Current Architecture Limitations

1. **Hardcoded Instruction Names**: Blocks portability
2. **Hardcoded Register Ordering**: ISA-specific logic
3. **Hardcoded Semantic Patterns**: RISC-V-specific code generation
4. **Large Functions**: Some functions are 200+ lines
5. **Code Duplication**: Many helper functions duplicated

### Recommendations for Generalization

See `BACKEND_ARCHITECTURE.md` for detailed recommendations:

1. **Priority 1**: Remove hardcoded names
2. **Priority 2**: Generalize register ordering
3. **Priority 3**: Generalize semantic generation
4. **Priority 4**: Extract duplicate code

---

## Additional Resources

- **BACKEND_ARCHITECTURE.md**: Detailed architecture analysis and generality assessment
- **Sail Language Manual**: [Sail Documentation](https://github.com/rems-project/sail)
- **CodAL Language**: Check your CodAL toolchain documentation
- **Example Files**: See `custom_riscv.sail` for examples
- **Reference Output**: See `isa_compare.codal` for reference CodAL structure

---

## Contributing

When modifying the backend:

1. **Test with simple examples first**: Use `custom_riscv.sail`
2. **Verify output manually**: Check generated CodAL files
3. **Test with full RISC-V**: Use `compile_riscv_insts_base.sh`
4. **Update documentation**: Update this README and `BACKEND_ARCHITECTURE.md`
5. **Check generality**: Consider impact on other ISAs

---

## License

[Add your license information here]

---

## Contact

[Add contact information or issue tracker link]

---

**Last Updated**: [Current Date]
**Version**: 1.0
**Author**: [Your Name/Team]

