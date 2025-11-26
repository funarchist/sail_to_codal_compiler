default Order dec

$include <prelude.sail>

$include "riscv_types_minimal.sail"

/*union clause ast = ITYPE :  (bits(12), regidx, regidx, iop)


mapping clause encdec = ITYPE(imm, rs1, rd, LLL) <-> imm @ encdec_reg(rs1) @ 000 @ encdec_reg(rd) @ 0b0101011
*/




/* Instruction type definitions */
union clause ast = RTYPE : (regidx, regidx, regidx, rop)

/* Binary encoding */
/*mapping clause encdec = RTYPE(rs2, rs1, rd, ADD)  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011*/
mapping clause encdec = RTYPE(rs2, rs1, rd, SUB)  <-> 0b0100000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, SLT)  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b010 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, SLTU) <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b011 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, AND)  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b111 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, OR)   <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b110 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, XOR)  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b100 @ encdec_reg(rd) @ 0b0110011
/*mapping clause encdec = RTYPE(rs2, rs1, rd, SLL)  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b001 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, SRL)  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b101 @ encdec_reg(rd) @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, SRA)  <-> 0b0100000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b101 @ encdec_reg(rd) @ 0b0110011 */



/* Execution semantics */
function clause execute (RTYPE(rs2, rs1, rd, op)) = {
  X(rd) = match op {
    /*ADD  => X(rs1) + X(rs2),*/
    SUB  => X(rs1) /*- X(rs2)*/,
    SLT  => zero_extend(bool_to_bits(X(rs1) <_s X(rs2))),
    SLTU => zero_extend(bool_to_bits(X(rs1) <_u X(rs2))), 
    AND  => X(rs1) & X(rs2),
    OR   => X(rs1) | X(rs2),
    XOR  => X(rs1) /*^ X(rs2)*/,
  /*  SLL  => X(rs1) << X(rs2)[log2_xlen - 1 .. 0],
    SRL  => X(rs1) >> X(rs2)[log2_xlen - 1 .. 0],
    SRA  => shift_bits_right_arith(X(rs1), X(rs2)[log2_xlen - 1 .. 0]), */
  };
  RETIRE_SUCCESS
}

mapping rtype_mnemonic : rop <-> string = {
  /*ADD  <-> "add",*/
  SUB  <-> "sub",
  SLT  <-> "slt",
  SLTU <-> "sltu",
  AND  <-> "and",
  OR   <-> "or",
  XOR  <-> "jol",
/*  SLL  <-> "sll",
  SRL  <-> "srl",
   SRA  <-> "sra" */
}

 Assembly syntax
mapping clause assembly = RTYPE(rs2, rs1, rd, op)
  <-> rtype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)



/* ****************************************************************** */
/*union clause ast = ITYPE : (bits(12), regidx, regidx, iop)

mapping encdec_iop : iop <-> bits(3) = {
  ADDI  <-> 0b000,
  SLTI  <-> 0b010,
  SLTIU <-> 0b011,
  ANDI  <-> 0b111,
  ORI   <-> 0b110,
  XORI  <-> 0b100
}

mapping clause encdec = ITYPE(imm, rs1, rd, op)
  <-> imm @ encdec_reg(rs1) @ encdec_iop(op) @ encdec_reg(rd) @ 0b0010011

function clause execute (ITYPE (imm, rs1, rd, op)) = {
  let immext : xlenbits = sign_extend(imm);
  X(rd) = match op {
    ADDI  => X(rs1) + immext,
    SLTI  => zero_extend(bool_to_bits(X(rs1) <_s immext)),
    SLTIU => zero_extend(bool_to_bits(X(rs1) <_u immext)),
    ANDI  => X(rs1) & immext,
    ORI   => X(rs1) | immext,
    XORI  => X(rs1) /*^ immext*/
  };
  RETIRE_SUCCESS
}

mapping itype_mnemonic : iop <-> string = {
  ADDI  <-> "addi",
  SLTI  <-> "slti",
  SLTIU <-> "sltiu",
  XORI  <-> "xori",
  ORI   <-> "ori",
  ANDI  <-> "andi"
}
*/
/*
mapping clause assembly = ITYPE(imm, rs1, rd, op)
  <-> itype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_signed_12(imm)
*/
/* ****************************************************************** */