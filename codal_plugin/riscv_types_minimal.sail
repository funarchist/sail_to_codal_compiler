/* Minimal RISC-V types for Codal backend compatibility */

/*Eclectic mix of riscv_reg_type.sail
riscv_regs.sail
riscv_types.sail





*/

$include <prelude.sail>




/* Type definitions */
newtype regidx = Regidx : bits(5)
type xlenbits = bits(32)

/* Helper function to extract bits from regidx */
val regidx_bits : regidx -> bits(5)
function regidx_bits(Regidx(b)) = b

/* default register type */
type regtype = xlenbits

/* Program counter */
register PC : xlenbits


/* default zero register 
let zero_reg : regtype = zeros()*/
newtype regno = Regno : range(0, 31)


/* Enum definitions */
enum rop = {/*ADD,*/  SUB , SLT ,  SLTU, XOR, /*SRL, SRA,SLL,*/ OR, AND}                   /* reg-reg ops */
enum iop =  {ADDI ,SLTI  ,SLTIU ,ANDI  ,ORI   ,XORI}
/* Scattered union declaration */
scattered union ast

/* Type signatures for scattered mappings */
val encdec : ast <-> bits(32)
val assembly : ast <-> string

/* Scattered mapping declarations */
scattered mapping encdec
scattered mapping assembly

/* Function declarations */
val execute : ast -> unit

/* Execution result - simplified for Codal backend */
let RETIRE_SUCCESS : unit = ()



/* Helper functions for encoding */
/*val reg_name : regidx -> string*/
val hex_bits_signed_12 : bits(12) -> string
val hex_bits_signed_20 : bits(20) -> string

/* mappings for assembly */

mapping reg_abi_name_raw : bits(5) <-> string = {
    0b00000 <-> "zero",
    0b00001 <-> "ra",
    0b00010 <-> "sp",
    0b00011 <-> "gp",
    0b00100 <-> "tp",
    0b00101 <-> "t0",
    0b00110 <-> "t1",
    0b00111 <-> "t2",
    0b01000 <-> "fp",
    0b01001 <-> "s1",
    0b01010 <-> "a0",
    0b01011 <-> "a1",
    0b01100 <-> "a2",
    0b01101 <-> "a3",
    0b01110 <-> "a4",
    0b01111 <-> "a5",
    0b10000 <-> "a6",
    0b10001 <-> "a7",
    0b10010 <-> "s2",
    0b10011 <-> "s3",
    0b10100 <-> "s4",
    0b10101 <-> "s5",
    0b10110 <-> "s6",
    0b10111 <-> "s7",
    0b11000 <-> "s8",
    0b11001 <-> "s9",
    0b11010 <-> "s10",
    0b11011 <-> "s11",
    0b11100 <-> "t3",
    0b11101 <-> "t4",
    0b11110 <-> "t5",
    0b11111 <-> "t6",
}


/*Overloaded write function*/

val xreg_full_write_callback = pure {c: "xreg_full_write_callback"} : (string, regidx, xlenbits) -> unit
function xreg_full_write_callback(_) = ()



/* register file and accessors */
register x0 : regtype /*i created*/
register x1  : regtype
register x2  : regtype
register x3  : regtype
register x4  : regtype
register x5  : regtype
register x6  : regtype
register x7  : regtype
register x8  : regtype
register x9  : regtype
register x10 : regtype
register x11 : regtype
register x12 : regtype
register x13 : regtype
register x14 : regtype
register x15 : regtype
register x16 : regtype
register x17 : regtype
register x18 : regtype
register x19 : regtype
register x20 : regtype
register x21 : regtype
register x22 : regtype
register x23 : regtype
register x24 : regtype
register x25 : regtype
register x26 : regtype
register x27 : regtype
register x28 : regtype
register x29 : regtype
register x30 : regtype
register x31 : regtype


/* conversions */

val regval_from_reg : regtype -> xlenbits
function regval_from_reg(r) = r

val regval_into_reg : xlenbits -> regtype
function regval_into_reg(v) = v

function rX (Regno(r) : regno) -> xlenbits = {
  let v : regtype =
    match r {
      0 => x0,
      1 => x1,
      2 => x2,
      3 => x3,
      4 => x4,
      5 => x5,
      6 => x6,
      7 => x7,
      8 => x8,
      9 => x9,
      10 => x10,
      11 => x11,
      12 => x12,
      13 => x13,
      14 => x14,
      15 => x15,
      16 => x16,
      17 => x17,
      18 => x18,
      19 => x19,
      20 => x20,
      21 => x21,
      22 => x22,
      23 => x23,
      24 => x24,
      25 => x25,
      26 => x26,
      27 => x27,
      28 => x28,
      29 => x29,
      30 => x30,
      31 => x31,
    };
  regval_from_reg(v)
}


/* Mappings for encoding */
mapping encdec_reg : regidx <-> bits(5) = { Regidx(r) <-> r }

/* Function definitions */
mapping reg_name : regidx <-> string = {
  Regidx(i)      <-> reg_abi_name_raw(i),
}



function xreg_write_callback(reg : regidx, value : xlenbits) -> unit = {
  let name = reg_name(reg);
  xreg_full_write_callback(name, reg, value);
}

val __raw_GetSlice_int = pure "get_slice_int" : forall 'w, 'w >= 0. (int('w), int, int) -> bits('w)

val to_bits : forall 'l, 'l >= 0.(implicit('l), int) -> bits('l)
function to_bits (l, n) = __raw_GetSlice_int(l, n, 0)

function wX (Regno(r) : regno, in_v : xlenbits) -> unit = {
  let v = regval_into_reg(in_v);
  match r {
    0  => (),
    1  => x1 = v,
    2  => x2 = v,
    3  => x3 = v,
    4  => x4 = v,
    5  => x5 = v,
    6  => x6 = v,
    7  => x7 = v,
    8  => x8 = v,
    9  => x9 = v,
    10 => x10 = v,
    11 => x11 = v,
    12 => x12 = v,
    13 => x13 = v,
    14 => x14 = v,
    15 => x15 = v,
    16 => x16 = v,
    17 => x17 = v,
    18 => x18 = v,
    19 => x19 = v,
    20 => x20 = v,
    21 => x21 = v,
    22 => x22 = v,
    23 => x23 = v,
    24 => x24 = v,
    25 => x25 = v,
    26 => x26 = v,
    27 => x27 = v,
    28 => x28 = v,
    29 => x29 = v,
    30 => x30 = v,
    31 => x31 = v,
  };
  if r != 0 then xreg_write_callback(Regidx(to_bits(r)), in_v)
}


function rX_bits(Regidx(i) : regidx) -> xlenbits = rX(Regno(unsigned(i)))


function wX_bits(Regidx(i) : regidx, data : xlenbits) -> unit = {
  wX(Regno(unsigned(i))) = data
}

overload X = {rX_bits, wX_bits, rX, wX }


mapping spc : unit <-> string = { () <-> " " }
mapping sep : unit <-> string = { () <-> "," }

function hex_bits_signed_12(imm) =  hex_str(unsigned(imm))  /*"x" + missing*/
function hex_bits_signed_20(imm) =  hex_str(unsigned(imm))  /*"x" + missing*/

/* Comparison operators for signed/unsigned NOT TRUE PLACEHOLDER*/
infix 4 <_s
infix 4 >=_s
infix 4 <_u
infix 4 >=_u

val operator <_s  : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator >=_s : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator <_u  : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator >=_u : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool

function operator <_s  (x, y) = signed(x) < signed(y)
function operator >=_s (x, y) = signed(x) >= signed(y)
function operator <_u  (x, y) = unsigned(x) < unsigned(y)
function operator >=_u (x, y) = unsigned(x) >= unsigned(y)

/* Helper functions for SLT/SLTU instructions */
val bool_to_bits : bool -> bits(1)
function bool_to_bits(x) = if x then 0b1 else 0b0

val zero_extend : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
function zero_extend(m, x) = sail_zero_extend(x, m)

val sign_extend : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
function sign_extend(m, x) = sail_sign_extend(x, m)

/* Shift helper for SRA - use Sail's built-in arithmetic shift */
val shift_bits_right_arith : forall 'n 'm, 'n >= 0 & 'm >= 0. (bits('n), bits('m)) -> bits('n)
function shift_bits_right_arith(x, y) = {
  /* Convert shift amount to integer and perform arithmetic right shift */
  let shift_amount = unsigned(y);
  sail_shiftright(x, shift_amount)
}

/* Constants for shift operations */
let log2_xlen : int = 5  /* log2(32) for RV32 */


