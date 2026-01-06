# CodAL Backend Architecture and Generality Analysis

## Overview

The backend translates Sail AST (Abstract Syntax Tree) directly into CodAL ISA descriptions without using intermediate representations like JIB. It extracts information from Sail's structural definitions and generates CodAL code.

## How the Backend Works

### High-Level Flow

```
Sail AST → Collection Phase → Translation Phase → Code Generation Phase → CodAL Output
```

### Phase 1: Collection (Lines 52-96)

The backend first **collects** structural information from the Sail AST:

#### 1.1 Union Clauses Collection (`collect_union_clauses`)
- **Purpose**: Extract instruction families (RTYPE, ITYPE, LOAD, STORE, etc.)
- **Input**: Sail AST definitions
- **Output**: Map from union type ID → list of union clause info
- **What it extracts**:
  - Constructor names (e.g., `RTYPE`, `ITYPE`)
  - Argument types (e.g., `regidx`, `bits(12)`)
  - Location information
- **Generality**: ✅ **Fully general** - works with any Sail union type definition

#### 1.2 Enum Literals Collection (`collect_enum_literals`)
- **Purpose**: Extract operation types (ADD, SUB, AND, OR, etc.)
- **Input**: Sail AST definitions
- **Output**: Map from enum type ID → list of enum member IDs
- **What it extracts**:
  - Enum type names (e.g., `rop`, `uop`)
  - Enum member names (e.g., `ADD`, `SUB`, `LUI`)
- **Generality**: ✅ **Fully general** - works with any Sail enum definition

#### 1.3 Mappings Collection (`collect_mappings`)
- **Purpose**: Extract Sail mapping definitions (`encdec`, `assembly`, etc.)
- **Input**: Sail AST definitions
- **Output**: Map from mapping ID → mapping info (clauses)
- **What it extracts**:
  - Mapping names (e.g., `encdec`, `assembly`)
  - Mapping clauses (bidirectional, forwards, backwards)
- **Generality**: ✅ **Fully general** - works with any Sail mapping definition

#### 1.4 Execute Clauses Collection (`collect_execute_clauses`)
- **Purpose**: Extract semantic function clauses for instruction execution
- **Input**: Sail AST definitions
- **Output**: List of (function_id, pexp) pairs
- **What it extracts**:
  - Function patterns (instruction constructors)
  - Function bodies (semantic expressions)
- **Generality**: ✅ **Fully general** - works with any Sail function definition

### Phase 2: Translation (`ast_to_codal`)

The backend then **translates** the collected information into CodAL:

#### 2.1 Opcode Extraction (`parse_encdec_clause`)
- **Purpose**: Extract opcode bit patterns from `encdec` mappings
- **How it works**:
  1. Finds `encdec` mapping in collected mappings
  2. Parses right-hand side patterns (bit concatenations)
  3. Extracts `func7`, `func3`, `opcode` fields
  4. Computes full opcode values
- **Generality**: ⚠️ **Partially general**
  - ✅ Works with any `encdec` mapping structure
  - ⚠️ Assumes specific bit widths (7-bit func7, 3-bit func3, 7-bit opcode)
  - ⚠️ Hardcoded handling for SHIFTIOP (6-bit func7 padding)

#### 2.2 Operand Extraction (`extract_operand_info_from_clause`)
- **Purpose**: Identify instruction operands (registers, immediates, enums)
- **How it works**:
  1. Extracts variable names from `encdec` left patterns
  2. Matches names with types from union clause arguments
  3. Classifies as Register, Immediate, Enum, or Other
  4. Infers immediate bit widths and signedness
- **Generality**: ✅ **Mostly general**
  - ✅ Works with any operand pattern
  - ⚠️ Hardcoded type names: `regidx`, `bits`
  - ⚠️ Assumes last argument is enum (for filtering)

#### 2.3 Assembly Syntax Extraction (`extract_assembly_order`)
- **Purpose**: Determine operand order in assembly syntax
- **How it works**:
  1. Finds `assembly` mapping clause
  2. Parses right-hand side expression/pattern
  3. Extracts `reg_name(...)` calls to determine order
  4. Falls back to left pattern order if parsing fails
- **Generality**: ✅ **Mostly general**.
  - ✅ Works with `MCL_forwards`, `MCL_backwards`, `MCL_bidir`
  - ⚠️ Assumes `reg_name` function name
  - ⚠️ Falls back to pattern order if expression parsing fails

#### 2.4 Binary Encoding Generation (`generate_binary_encoding_template`)
- **Purpose**: Generate CodAL binary encoding strings
- **How it works**:
  1. Parses `encdec` right-hand side `MP_vector_concat`
  2. Identifies bit literals, `encdec_reg` calls, immediates
  3. Generates CodAL bitfield macros (`FUNC7`, `FUNC3`, `OPCODE`)
  4. Handles immediate splitting (STORE, BTYPE, JAL)
- **Generality**: ⚠️ **Partially general**
  - ✅ Works with any `MP_vector_concat` pattern
  - ⚠️ Hardcoded immediate splitting for specific instruction types
  - ⚠️ Assumes specific bitfield positions

#### 2.5 Semantic Translation (`translate_exp`)
- **Purpose**: Translate Sail expressions to CodAL
- **How it works**:
  1. Pattern matches Sail AST expression nodes
  2. Maps Sail functions to CodAL operators:
     - `add_bits` → `+`
     - `sub_vec` → `-`
     - `xor_vec` → `^`
     - `shift_bits_left` → `<<`
     - etc.
  3. Handles type casts, comparisons, extensions
- **Generality**: ⚠️ **Partially general**
  - ✅ Works with standard Sail expression patterns
  - ⚠️ Hardcoded function name mappings
  - ⚠️ RISC-V-specific constants (`log2_xlen`, `xlen`, `xlen_bytes`)

### Phase 3: Code Generation

The backend generates CodAL code:

#### 3.1 Opcode Header Generation (`generate_opcodes_header`)
- **Purpose**: Generate `opcodes.hcodal` with enum definitions
- **How it works**:
  1. Groups opcodes by instruction family
  2. Computes enum width dynamically
  3. Generates enum type and values
- **Generality**: ✅ **Mostly general**
  - ✅ Dynamically computes widths
  - ⚠️ Hardcoded family name mappings (SHIFTIOP → IMM_SHIFT, etc.)

#### 3.2 Instruction Element Generation (`generate_instruction_element`)
- **Purpose**: Generate CodAL `element` blocks for instructions
- **How it works**:
  1. Generates `use` declarations
  2. Generates assembly syntax
  3. Generates binary encoding
  4. Generates semantics (switch statement with cases)
- **Generality**: ⚠️ **Partially general**
  - ✅ Uses extracted operand info
  - ⚠️ Hardcoded register ordering logic per instruction type
  - ⚠️ Hardcoded semantics generation for specific types (BTYPE, LOAD, STORE, JAL, JALR)

## Generality Assessment

### ✅ Fully General (Works with any Sail ISA)

1. **AST Collection Functions**
   - `collect_union_clauses` - Any union type
   - `collect_enum_literals` - Any enum type
   - `collect_mappings` - Any mapping definition
   - `collect_execute_clauses` - Any function definition

2. **Pattern Extraction**
   - `extract_variable_names_from_pattern` - Any pattern structure
   - `extract_operand_info_from_clause` - Any operand pattern (with minor assumptions)
   - `extract_reg_names_from_expression` - Any expression structure
   - `extract_reg_names_from_mpat` - Any mapping pattern

3. **Dynamic Width Computation**
   - `compute_opcode_width` - Computes from pattern structure

### ⚠️ Partially General (Works with similar ISAs)

1. **Type Name Assumptions**
   - Assumes `regidx` for register types
   - Assumes `bits(N)` for immediate types
   - Assumes last argument is enum (for filtering)

2. **Bit Width Assumptions**
   - Assumes 7-bit func7, 3-bit func3, 7-bit opcode
   - Special handling for 6-bit func7 (SHIFTIOP)

3. **Function Name Mappings**
   - Hardcoded Sail → CodAL function mappings
   - RISC-V-specific constants

4. **Semantic Patterns**
   - Assumes specific semantic structures
   - Hardcoded handling for comparisons, shifts, extensions

### ❌ RISC-V Specific (Hardcoded)

1. **Instruction Family Names**
   - Hardcoded: `RTYPE`, `ITYPE`, `LOAD`, `STORE`, `BTYPE`, `UTYPE`, `JAL`, `JALR`, `SHIFTIOP`
   - Hardcoded family name mappings (SHIFTIOP → IMM_SHIFT, etc.)

2. **Register Ordering Logic**
   - Hardcoded per instruction type:
     - RTYPE: reverse rs2, rs1 to get rs1, rs2
     - BTYPE/STORE: reverse rs2, rs1
     - SHIFTIOP: reverse rd, rs1
   - Location: Lines ~1889-1922

3. **Semantics Generation**
   - Hardcoded for specific instruction types:
     - BTYPE: `if (result) write_pc(target_address)`
     - LOAD: `load(opc, address)`
     - STORE: `store(opc, address, result)`
     - JAL/JALR: PC manipulation
   - Location: Lines ~2105-2129

4. **Immediate Splitting**
   - Hardcoded for STORE, BTYPE, JAL
   - Location: `generate_binary_encoding_template`

5. **Family Priority/Ordering**
   - Hardcoded output order
   - Location: `get_family_priority`

## Portability to Other ISAs

### What Would Work Automatically

- ✅ ARM: If it uses similar union/enum/mapping structure
- ✅ MIPS: If it uses similar patterns
- ✅ x86: Would need significant adaptation

### What Would Need Changes

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

5. **Function Name Mappings** (Low Priority)
   - Current: Hardcoded Sail → CodAL mappings
   - Needed: Configuration file or pattern matching

## Current Architecture Strengths

1. **Direct AST Translation**: No intermediate representation
2. **Pattern-Based Extraction**: Works with Sail's structural patterns
3. **Dynamic Width Computation**: Computes opcode widths from patterns
4. **Modular Design**: Separate collection, translation, generation phases

## Current Architecture Limitations

1. **Hardcoded Instruction Names**: Blocks portability
2. **Hardcoded Register Ordering**: ISA-specific logic
3. **Hardcoded Semantic Patterns**: RISC-V-specific code generation
4. **Duplicate Code**: Many helper functions duplicated
5. **Large Functions**: Some functions are 200+ lines

## Recommendations for Generalization

### Priority 1: Remove Hardcoded Names
- Extract instruction family names from AST
- Use configuration or pattern matching instead of hardcoded strings

### Priority 2: Generalize Register Ordering
- Extract from assembly mapping patterns
- Use operand position information

### Priority 3: Generalize Semantic Generation
- More generic expression translation
- Pattern-based semantic code generation

### Priority 4: Extract Duplicate Code
- Consolidate helper functions
- Reduce code duplication

## Conclusion

The backend is **~60% general**:
- ✅ Collection phase: Fully general
- ✅ Pattern extraction: Mostly general
- ⚠️ Translation phase: Partially general
- ❌ Code generation: RISC-V specific

To make it fully general, the main work needed is:
1. Remove hardcoded instruction family names
2. Generalize register ordering logic
3. Make semantic generation more pattern-based
4. Extract and consolidate duplicate code

