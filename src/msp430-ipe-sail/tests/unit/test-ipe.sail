let ipe_start : Address = 0x2000
let ipe_end : Address = 0x3000

let pc_out : wordBits = 0x1000
let pc_in : wordBits = 0x2500

register ctl : wordBits

val mpu_reg_addr : (mpu_register_name) -> Address
function mpu_reg_addr(reg) = mpu_reg_base + 2 * mpu_register_index(reg)

val setup_ipe : (unit) -> unit
function setup_ipe() = {
  // MPU password
  Xmem(BYTE_INSTRUCTION, add_bits(mpu_reg_addr(MPUCTL0), 0x0001)) = Byte(0xA5);

  Xmem(WORD_INSTRUCTION, mpu_reg_addr(MPUIPSEGB1)) = Word(ipe_start >> 4);
  Xmem(WORD_INSTRUCTION, mpu_reg_addr(MPUIPSEGB2)) = Word(ipe_end >> 4);

  ctl = 0x0000;
  ctl[MPUIPENA_bit] = bitone;
  Xmem(WORD_INSTRUCTION, mpu_reg_addr(MPUIPC0)) = Word(ctl);

  print_endline("IPE enabled");
}


val test_trusted_access : (unit) -> unit
function test_trusted_access() = {
  print_endline("testing access with PC in IPE region");

  PC_reg = pc_in;

  print_endline("...to non-IPE region");
  writeMem(WORD_INSTRUCTION, sub_bits(ipe_start, 0x0010)) = Word(0x0022);
  assert(Xmem(WORD_INSTRUCTION, sub_bits(ipe_start, 0x0010)) == Word(0x0022));

  print_endline("...to IPE region");
  Xmem(WORD_INSTRUCTION, add_bits(ipe_start, 0x0010)) = Word(0x0022);
  assert(Xmem(WORD_INSTRUCTION, add_bits(ipe_start, 0x0010)) == Word(0x0022));
}

val test_untrusted_access : (unit) -> unit
function test_untrusted_access() = {
  print_endline("testing access with PC outside IPE region");

  PC_reg = pc_out;

  print_endline("...to non-IPE region");
  Xmem(WORD_INSTRUCTION, sub_bits(ipe_start, 0x0010)) = Word(0x0011);
  assert(Xmem(WORD_INSTRUCTION, sub_bits(ipe_start, 0x0010)) == Word(0x0011));

  print_endline("...to IPE region");

  try {
    Xmem(WORD_INSTRUCTION, add_bits(ipe_start, 0x0010)) = Word(0x0000);
    throw test_fail("illegal IPE write was allowed")
  } catch {
    ipe_violation(_) => ()
  };

  try {
    let _ = Xmem(WORD_INSTRUCTION, add_bits(ipe_start, 0x0010));
    throw test_fail("illegal IPE read was allowed")
  } catch {
    ipe_violation(_) => ()
  }
}

val test_ipe_lock : (unit) -> unit
function test_ipe_lock() = {
  print_endline("testing change to IPE boundary");

  PC_reg = pc_out;
  Xmem(WORD_INSTRUCTION, mpu_reg_addr(MPUIPSEGB1)) = Word(add_bits(ipe_start, 0x0100) >> 4);
  Xmem(WORD_INSTRUCTION, add_bits(ipe_start, 0x0010)) = Word(0x0011);
  assert(Xmem(WORD_INSTRUCTION, add_bits(ipe_start, 0x0010)) == Word(0x0011));

  print_endline("testing disabling of IPE");

  Xmem(WORD_INSTRUCTION, mpu_reg_addr(MPUIPC0)) = Word(0x0000);
  Xmem(WORD_INSTRUCTION, sub_bits(ipe_end, 0x0010)) = Word(0x0013);
  assert(Xmem(WORD_INSTRUCTION, sub_bits(ipe_end, 0x0010)) == Word(0x0013));

  print_endline("testing locking of IPE registers");

  ctl = 0x0000;
  ctl[MPUIPENA_bit] = bitone;
  ctl[MPUIPLOCK_bit] = bitone;
  Xmem(WORD_INSTRUCTION, mpu_reg_addr(MPUIPSEGB1)) = Word(ipe_start >> 4);
  Xmem(WORD_INSTRUCTION, mpu_reg_addr(MPUIPC0)) = Word(ctl);

  try {
    Xmem(WORD_INSTRUCTION, add_bits(ipe_start, 0x0010)) = Word(0x0000);
    throw test_fail("illegal IPE write was allowed");
  } catch {
    ipe_violation(_) => ()
  };

  print_endline("testing writes to locked registers");
  Xmem(WORD_INSTRUCTION, mpu_reg_addr(MPUIPSEGB1)) = Word(0x0000);
  assert(Xmem(WORD_INSTRUCTION, mpu_reg_addr(MPUIPSEGB1)) == Word(ipe_start >> 4));
  Xmem(WORD_INSTRUCTION, mpu_reg_addr(MPUIPSEGB2)) = Word(0x0000);
  assert(Xmem(WORD_INSTRUCTION, mpu_reg_addr(MPUIPSEGB2)) == Word(ipe_end >> 4));
  Xmem(WORD_INSTRUCTION, mpu_reg_addr(MPUIPC0)) = Word(0x0000);
  assert(Xmem(WORD_INSTRUCTION, mpu_reg_addr(MPUIPC0)) == Word(ctl));
}

val test_boundary_access : (unit) -> unit
function test_boundary_access() = {
  print_endline("testing various boundary conditions");

  PC_reg = ipe_start + 0x0006;

  try {
    let _ = Xmem(WORD_INSTRUCTION, add_bits(ipe_start, 0x0010));
    throw test_fail("IPE read was allowed with PC in first 8 bytes of IPE")
  } catch {
    ipe_violation(_) => ()
  };

  PC_reg = ipe_end;

  try {
    let _ = Xmem(WORD_INSTRUCTION, add_bits(ipe_start, 0x0010));
    throw test_fail("IPE read was allowed with PC at IPE end")
  } catch {
    ipe_violation(_) => ()
  };

  PC_reg = pc_out;

  try {
    let _ = Xmem(WORD_INSTRUCTION, sub_bits(ipe_start, 0x0001));
    let _ = Xmem(WORD_INSTRUCTION, sub_bits(ipe_end, 0x0001));
    throw test_fail("word read that partially overlaps IPE was allowed")
  } catch {
    ipe_violation(_) => ()
  };

  // TODO partially overlapping word write?

  try {
    let _ = Xmem(BYTE_INSTRUCTION, ipe_start);
    let _ = Xmem(BYTE_INSTRUCTION, sub_bits(ipe_end, 0x0001));
    throw test_fail("byte read in IPE was allowed")
  } catch {
    ipe_violation(_) => ()
  };

}


val test_ipe : (unit) -> unit
function test_ipe() = {
  print_endline("\n\n    +-------------------+");
  print_endline("    |    TESTING IPE    |");
  print_endline("    +-------------------+\n");

  try {
    setup_ipe();
    test_trusted_access();
    test_untrusted_access();
    test_ipe_lock();
    test_boundary_access();
  } catch {
    test_fail(msg) => { print_endline("TEST FAILED: " + msg); exit(()) }
  };

  // TODO ivt, execute access
}
