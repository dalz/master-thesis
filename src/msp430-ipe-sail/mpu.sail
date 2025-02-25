let mpu_reg_base : Address = 0x05A0 // MSP430FR5969

enum mpu_register_name = {
  // MPU control registers
  MPUCTL0,
  MPUCTL1,

  // MPU segment borders
  MPUSEGB2,
  MPUSEGB1,

  // MPU segment access flags
  MPUSAM,

  // IPE
  MPUIPC0,    // control register
  MPUIPSEGB2, // 16 msb of upper border (not included)
  MPUIPSEGB1, // 16 msb of lower border (included)
}

mapping mpu_register_index : mpu_register_name <-> range(0, 7) = {
  MPUCTL0    <-> 0,
  MPUCTL1    <-> 1,
  MPUSEGB2   <-> 2,
  MPUSEGB1   <-> 3,
  MPUSAM     <-> 4,
  MPUIPC0    <-> 5,
  MPUIPSEGB2 <-> 6,
  MPUIPSEGB1 <-> 7,
}

// MPU control register 0 (MPUCTL0)
let MPUPW_high   = 15 // allows writing MPU registers when correct
let MPUPW_low    = 8
// let MPUSEGIE_bit = 4
let MPULOCK_bit  = 1  // if 1 prevents writes on MPU regs, except MPUCTL1 and IPE regs
// let MPUENA_bit   = 0  // enable MPU

// MPU control register 1 (MPUCTL1)
// let MPUSEGIPIFG_bit = 4
// let MPUSEGIIFG_bit  = 3
// let MPUSEG3IFG_bit  = 2
// let MPUSEG2IFG_bit  = 1
// let MPUSEG1IFG_bit  = 0

// MPU segmentation access register (MPUSAM)
// let MPUSEGIE_bit = 4
// let MPULOCK_bit = 1

// IPE control register (MPUIPC0)
let MPUIPLOCK_bit = 7 // if 1, prevents writes on IPE registers
let MPUIPENA_bit  = 6 // enable IPE
let MPUIPVS_bit   = 5 // violation select: wether a PUC occurs on IPE violations

register MPUCTL0_reg    : wordBits
register MPUCTL1_reg    : wordBits
register MPUSEGB2_reg   : wordBits
register MPUSEGB1_reg   : wordBits
register MPUSAM_reg     : wordBits
register MPUIPC0_reg    : wordBits
register MPUIPSEGB2_reg : wordBits
register MPUIPSEGB1_reg : wordBits

val is_mpu_reg_addr : (Address) -> bool
function is_mpu_reg_addr(addr) =
  let off : int = unsigned(addr) - unsigned(mpu_reg_base) in
  off >= 0 & off < 16

val read_mpu_reg_byte : (Address) -> byteBits
function read_mpu_reg_byte(addr) =
  let off : int = unsigned(addr) - unsigned(mpu_reg_base) in
  if off >= 0 & off < 16 then

  let w : wordBits = match mpu_register_index(off / 2) {
    MPUCTL0    => [MPUCTL0_reg with MPUPW_high..MPUPW_low = 0x96], // MPUPW always reads as 0x96
    MPUCTL1    => MPUCTL1_reg,
    MPUSEGB2   => MPUSEGB2_reg,
    MPUSEGB1   => MPUSEGB1_reg,
    MPUSAM     => MPUSAM_reg,
    MPUIPC0    => MPUIPC0_reg,
    MPUIPSEGB2 => MPUIPSEGB2_reg,
    MPUIPSEGB1 => MPUIPSEGB1_reg,
  }
  in if off % 2 == 0 then w[7..0] else w[15..8]

  // TODO reserved bits always read zero (apply a mask if register has reserved bits)

  // can't put the guard in the assert (instead of if-else with trivial assert)
  // because sail --katamaran doesn't take that into account for type inference
  else { assert(false); 0x00 }


// returns true if given index of a register that is locked by the MPULOCK flag
val is_lockable_mpu_reg : (mpu_register_name) -> bool
function is_lockable_mpu_reg(reg) =
  match reg {
    MPUCTL0  => true,
    MPUSEGB2 => true,
    MPUSEGB1 => true,
    MPUSAM   => true,
    _        => false
  }

val is_ipe_reg : (mpu_register_name) -> bool
function is_ipe_reg(reg) =
  match reg {
    MPUIPC0    => true,
    MPUIPSEGB1 => true,
    MPUIPSEGB2 => true,
    _          => false
  }

val write_mpu_reg_byte : (Address, byteBits) -> unit
function write_mpu_reg_byte(addr, v) =
  let off : int = unsigned(addr) - unsigned(mpu_reg_base) in
  if off >= 0 & off < 16 then
    let reg = mpu_register_index(off / 2) in
    let reg_is_not_MPUCTL0 : bool = match reg { MPUCTL0 => false, _ => true } in

    // prevent writes when password is wrong (except for writing the password itself)
    // TODO word writes with wrong password should be disallowed,
    // now it works if the low byte of the word written is the correct password
    // and the address is that of MPUPW
    if MPUCTL0_reg[MPUPW_high..MPUPW_low] != 0xA5
       & (reg_is_not_MPUCTL0 | off % 2 == 0)
    then throw power_up_clear()

    // prevent write on locked registers
    else if (is_lockable_mpu_reg(reg) & MPUCTL0_reg[MPULOCK_bit] == bitone)
          | (is_ipe_reg(reg) & MPUIPC0_reg[MPUIPLOCK_bit] == bitone)
    then ()

    // write high / low byte of register
    else if off % 2 == 0
    then match reg {
        MPUCTL0    => MPUCTL0_reg[7..0] = v,
        MPUCTL1    => MPUCTL1_reg[7..0] = v,
        MPUSEGB2   => MPUSEGB2_reg[7..0] = v,
        MPUSEGB1   => MPUSEGB1_reg[7..0] = v,
        MPUSAM     => MPUSAM_reg[7..0] = v,
        MPUIPC0    => MPUIPC0_reg[7..0] = v,
        MPUIPSEGB2 => MPUIPSEGB2_reg[7..0] = v,
        MPUIPSEGB1 => MPUIPSEGB1_reg[7..0] = v,
    }
    else match reg {
        MPUCTL0    => MPUCTL0_reg[15..8] = v,
        MPUCTL1    => MPUCTL1_reg[15..8] = v,
        MPUSEGB2   => MPUSEGB2_reg[15..8] = v,
        MPUSEGB1   => MPUSEGB1_reg[15..8] = v,
        MPUSAM     => MPUSAM_reg[15..8] = v,
        MPUIPC0    => MPUIPC0_reg[15..8] = v,
        MPUIPSEGB2 => MPUIPSEGB2_reg[15..8] = v,
        MPUIPSEGB1 => MPUIPSEGB1_reg[15..8] = v,
    }

  else assert(false)

val ipe_lower : (unit) -> int
function ipe_lower() = unsigned(MPUIPSEGB1_reg) * 16

val ipe_higher : (unit) -> int
function ipe_higher() = unsigned(MPUIPSEGB2_reg) * 16

val in_ipe_segment : (Address) -> bool
function in_ipe_segment(addr) =
  ipe_lower() <= unsigned(addr)
  & unsigned(addr) < ipe_higher()

val in_ivt_or_rv : (Address) -> bool
function in_ivt_or_rv(addr) =
  unsigned(0xFF80) <= unsigned(addr)
  & unsigned(addr) <= unsigned(0xFFFF)

enum access_mode = R | W | X

val is_x : (access_mode) -> bool
function is_x(m) = match m { X => true, _ => false }

val check_ipe_access : (Address, access_mode) -> bool
function check_ipe_access(addr, m) =
  let pc = unsigned(PC_reg) in
  // allow access if...
  // ...IPE disabled, or
  MPUIPC0_reg[MPUIPENA_bit] == bitzero
  // ...address not protected, or
  | ~(in_ipe_segment(addr))
  | (// ...PC in IPE segment except first 8 bytes, and
     (ipe_lower() + 8 <= pc & pc < ipe_higher())
     // not execute access in IVT or RV (9.4.1)
     & ~(is_x(m) & in_ivt_or_rv(addr)))

// TODO interrupt vector?

val check_byte_access : (Address, access_mode) -> unit
function check_byte_access(addr, m) =
  if ~(check_ipe_access(addr, m)) then throw ipe_violation(addr)

// TODO brownout reset?
// doesn't seem to be implemented
// disables MPU
// clears MPULOCK and MPUIPLOCK
