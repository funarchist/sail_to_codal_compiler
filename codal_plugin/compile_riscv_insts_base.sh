#!/bin/bash
# Compile riscv_insts_base.sail to CodAL with all necessary dependencies
# This follows the same file inclusion order as the C backend

cd "$(dirname "$0")/../sail-riscv/model" || exit 1

# Build the plugin first
cd ../../codal_plugin || exit 1
dune build sail_plugin_codal_gold.cmxs || exit 1
cd ../sail-riscv/model || exit 1

# Sail compiler command with all dependencies in correct order
# This matches the order from CMakeLists.txt for sail_arch_srcs + sail_seq_inst_srcs
# Run sail compilation and capture exit status
if sail --plugin ../../codal_plugin/_build/default/sail_plugin_codal_gold.cmxs \
  --codal \
  prelude.sail \
  riscv_errors.sail \
  riscv_xlen32.sail \
  riscv_xlen.sail \
  riscv_flen_F.sail \
  riscv_flen.sail \
  riscv_vlen.sail \
  prelude_mem_addrtype.sail \
  prelude_mem_metadata.sail \
  prelude_mem.sail \
  arithmetic.sail \
  rvfi_dii.sail \
  rvfi_dii_v1.sail \
  rvfi_dii_v2.sail \
  riscv_extensions.sail \
  riscv_types_common.sail \
  riscv_types_ext.sail \
  riscv_types.sail \
  riscv_vmem_types.sail \
  riscv_csr_begin.sail \
  riscv_callbacks.sail \
  riscv_reg_type.sail \
  riscv_freg_type.sail \
  riscv_regs.sail \
  riscv_pc_access.sail \
  riscv_sys_regs.sail \
  riscv_pmp_regs.sail \
  riscv_pmp_control.sail \
  riscv_ext_regs.sail \
  riscv_addr_checks_common.sail \
  riscv_addr_checks.sail \
  riscv_misa_ext.sail \
  riscv_vreg_type.sail \
  riscv_vext_regs.sail \
  riscv_vext_control.sail \
  riscv_sys_exceptions.sail \
  riscv_sync_exception.sail \
  riscv_zihpm.sail \
  riscv_sscofpmf.sail \
  riscv_zkr_control.sail \
  riscv_zicntr_control.sail \
  riscv_softfloat_interface.sail \
  riscv_fdext_regs.sail \
  riscv_fdext_control.sail \
  riscv_smcntrpmf.sail \
  riscv_sys_reservation.sail \
  riscv_sys_control.sail \
  riscv_platform.sail \
  riscv_sstc.sail \
  riscv_mem.sail \
  riscv_inst_retire.sail \
  riscv_vmem_pte.sail \
  riscv_vmem_ptw.sail \
  riscv_vmem_tlb.sail \
  riscv_vmem.sail \
  riscv_vmem_utils.sail \
  riscv_insts_begin.sail \
  riscv_insts_base.sail \
  ../../codal_plugin/custom_riscv.sail \
  -o riscv_insts_base_codal 2>&1; then
  echo "✓ Compilation successful!"
  echo "Generated files:"
  ls -lh riscv_insts_base_codal.codal 2>/dev/null && echo "  - riscv_insts_base_codal.codal"
  ls -lh ../../codal_plugin/opcodes.hcodal 2>/dev/null && echo "  - codal_plugin/opcodes.hcodal"
else
  echo "✗ Compilation failed or had errors (see output above)"
  exit 1
fi

