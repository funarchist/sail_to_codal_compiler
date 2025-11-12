# Sail Codal Backend

This backend transforms Sail code to Codal-compatible C code, with the key feature of converting Sail's `int` type to `sail_int`.

## Features

- **Type Transformation**: Converts Sail `int` types to `sail_int`
- **Complete Sail Support**: Handles all Sail language constructs
- **Codal Integration**: Generates C code compatible with Codal framework
- **Memory Management**: Proper allocation and deallocation of Sail types

## Usage

To compile a Sail file using the Codal backend:

```bash
sail -codal input.sail -o output.c
```

## Type Mappings

| Sail Type | Codal Type |
|-----------|------------|
| `int` | `sail_int` |
| `int(n)` | `int64_t` (n≤64) or `sail_int` |
| `nat` | `sail_int` |
| `bit` | `bool` |
| `bool` | `bool` |
| `unit` | `void` |
| `string` | `char*` |
| `real` | `sail_real` |
| `bits(n)` | `sail_bits` |
| `vector(n, t)` | `sail_vector_*` |
| `list(t)` | `sail_list_*` |

## Example Transformation

**Input Sail:**
```sail
function add(x : int, y : int) -> int = {
  return x + y;
}
```

**Generated Codal C:**
```c
sail_int add(sail_int x, sail_int y) {
  return sail_int_add(x, y);
}
```

## Key Functions

- `codal_type_of_ctyp`: Converts Jib types to Codal C types
- `codal_value_of_cval`: Converts Jib values to Codal C expressions
- `codal_instr_of_instr`: Converts Jib instructions to Codal C statements
- `emit_codal`: Main entry point for code generation

## Dependencies

The backend requires:
- `sail` library
- `jib_util` for Jib utilities
- `jib_compile` for Jib compilation
- `type_check` for type checking
- `ast_util` for AST utilities

## Building

To build the Codal backend:

```bash
dune build src/sail_codal_backend/
```

## Testing

Test the backend with the provided test file:

```bash
sail -codal test_codal.sail -o test_codal.c
```

This will generate Codal-compatible C code with all `int` types transformed to `sail_int`. 