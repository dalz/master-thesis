let mpu_reg_base : Address = 0x05A0 // MSP430FR5969

bitfield mpu_register_data : bits(16) = {
  HIGH : 15 .. 8,
  LOW  :  7 .. 0,

  // MPU control register 0 (MPUCTL0)
  MPUPW    : 15 .. 8, // allows writing MPU registers when correct
  MPUSEGIE : 4,       // TODO
  MPULOCK  : 1,       // if 1, prevents writes on MPU registers
                      //   except MPUCTL1 and the IPE registers
  MPUENA   : 0,       // TODO enable MPU

  // MPU control register 1 (MPUCTL1) TODO
  MPUSEGIPIFG : 4,
  MPUSEGIIFG  : 3,
  MPUSEG3IFG  : 2,
  MPUSEG2IFG  : 1,
  MPUSEG1IFG  : 0,

  // MPU segmentation access register (MPUSAM) TODO

  // IPE control register (MPUIPC0)
  MPUIPLOCK : 7, // if 1, prevents writes on IPE registers
  MPUIPENA  : 6, // enable IPE
  MPUIPVS   : 5, // violation select: wether a PUC occurs on IPE violations
}

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

register mpu_registers : vector(8, mpu_register_data)

val get_mpu_reg : (mpu_register_name) -> mpu_register_data
function get_mpu_reg(reg) =
  mpu_registers[mpu_register_index(reg)]

val is_mpu_reg_addr : (Address) -> bool
function is_mpu_reg_addr(addr) =
  let off : int = unsigned(addr) - unsigned(mpu_reg_base) in
  off >= 0 & off < 16

val read_mpu_reg_byte : (Address) -> byteBits
function read_mpu_reg_byte(addr) =
  let off : int = unsigned(addr) - unsigned(mpu_reg_base) in
  if off >= 0 & off < 16 then

  // TODO reserved bits always read zero (apply a mask if register has reserved bits)

  match mpu_register_index(off / 2) {
    MPUCTL0 if off % 2 == 1 => 0x96, // MPUPW always reads as 0x96

    _ =>
      let v = mpu_registers[off / 2] in
      if off % 2 == 0 then v[LOW] else v[HIGH]
  }

  // can't put the guard in the assert (instead of if-else with trivial assert)
  // because sail --katamaran doesn't take that into account for type inference
  else { assert(false); 0x00 }


// returns true if given index of a register that is locked by the MPULOCK flag
val is_lockable_mpu_reg_idx : (range(0, 7)) -> bool
function is_lockable_mpu_reg_idx(idx) =
  match mpu_register_index(idx) {
    MPUCTL0  => true,
    MPUSEGB2 => true,
    MPUSEGB1 => true,
    MPUSAM   => true,
    _        => false
  }

val is_ipe_reg_idx : (range(0, 7)) -> bool
function is_ipe_reg_idx(idx) =
  match mpu_register_index(idx) {
    MPUIPC0    => true,
    MPUIPSEGB1 => true,
    MPUIPSEGB2 => true,
    _          => false
  }

val write_mpu_reg_byte : (Address, byteBits) -> unit
function write_mpu_reg_byte(addr, v) =
  let off : int = unsigned(addr) - unsigned(mpu_reg_base) in
  if off >= 0 & off < 16 then
    let idx = off / 2 in
    
    // prevent writes when password is wrong (except for writing the password itself)
    // TODO word writes with wrong password should be disallowed,
    // now it works if the low byte of the word written is the correct password
    // and the address is that of MPUPW
    if get_mpu_reg(MPUCTL0)[MPUPW] != 0xA5
       & (idx != mpu_register_index(MPUCTL0) | off % 2 == 0)
    then throw notImplemented("mpu write with wrong password") // TODO PUC
    
    // prevent write on locked registers
    else if (is_lockable_mpu_reg_idx(idx) & get_mpu_reg(MPUCTL0)[MPULOCK] == 0b1)
          | (is_ipe_reg_idx(idx) & get_mpu_reg(MPUIPC0)[MPUIPLOCK] == 0b1)
    then throw notImplemented("access to locked register") // TODO what should happen?
    
    // read high / low byte of register
    else if off % 2 == 0
    then mpu_registers[idx] = [mpu_registers[idx] with LOW = v]
    else mpu_registers[idx] = [mpu_registers[idx] with HIGH = v]

  else assert(false)

val ipe_lower : (unit) -> int
function ipe_lower() = unsigned(get_mpu_reg(MPUIPSEGB1).bits) * 16

val ipe_higher : (unit) -> int
function ipe_higher() = unsigned(get_mpu_reg(MPUIPSEGB2).bits) * 16

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
  get_mpu_reg(MPUIPC0)[MPUIPENA] == 0b0
  // ...address not protected, or
  | ~(in_ipe_segment(addr))
  | (// ...PC in IPE segment except first 8 bytes, and
     (ipe_lower() + 8 <= pc & pc < ipe_higher())
     // not execute access in IVT or RV (9.4.1)
     & ~(is_x(m) & in_ivt_or_rv(addr)))

// TODO interrupt vector?

val check_byte_access : (Address, access_mode) -> bool
function check_byte_access(addr, m) = check_ipe_access(addr, m)

// TODO brownout reset?
// doesn't seem to be implemented
// disables MPU
// clears MPULOCK and MPUIPLOCK
