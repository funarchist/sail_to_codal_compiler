

mapping clause encdec = RTYPE(rs2, rs1, rd, FKK)  <-> 0b0000000 @ encdec_reg(rs2) @ encdec_reg(rs1) @ 0b000 @ encdec_reg(rd) @ 0b0001011

function clause execute (RTYPE(rs2, rs1, rd, op)) = {
  X(rd) = match op {
    FKK  => X(rs1) - X(rs2),
  };
  RETIRE_SUCCESS
}

