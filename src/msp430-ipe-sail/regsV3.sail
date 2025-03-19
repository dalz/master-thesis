//https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=49
//3.3 Addressing Modes
mapping sourcemaping: AM <-> addressingModeSourceBits = {
  REGISTER_MODE <-> 0b00,
  INDEXED_MODE <-> 0b01,
  INDIRECT_REGISTER_MODE <-> 0b10,
  INDIRECT_AUTOINCREMENT_MODE <-> 0b11,
}

//https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=49
//3.3 Addressing Modes
mapping destinationmaping: AM <-> addressingModeDestinationBits = {
  REGISTER_MODE <-> 0b0,
  INDEXED_MODE <-> 0b1,
}

register LastInstructionFetch : WordByte = Word(undefined) /* program counter */

val readReg: (BW, Register) -> WordByte
function readReg(bw, reg) = match bw {
  WORD_INSTRUCTION =>
    Word(match reg {
      PC    =>    PC_reg,
      SP    =>    SP_reg,
      SRCG1 => SRCG1_reg,
      CG2   =>   CG2_reg,
      R4    =>    R4_reg,
      R5    =>    R5_reg,
      R6    =>    R6_reg,
      R7    =>    R7_reg,
      R8    =>    R8_reg,
      R9    =>    R9_reg,
      R10   =>   R10_reg,
      R11   =>   R11_reg,
      R12   =>   R12_reg,
      R13   =>   R13_reg,
      R14   =>   R14_reg,
      R15   =>   R15_reg,
    }),

  BYTE_INSTRUCTION =>
    let Word(value) : WordByte = readReg(WORD_INSTRUCTION, reg) in
    Byte(value[7 .. 0])
}

function writeReg(bw, reg, v) = {
  let v : wordBits = match v {
    Word(v) => v,
    Byte(v) => sail_zero_extend(v, 16)
  }
  in

  let v : wordBits = match bw {
    WORD_INSTRUCTION => v,
    BYTE_INSTRUCTION =>
      // https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=48
      // 3.2.5 General-Purpose Registers R4 to R15
      // writing in all modes will override the high byte
      sail_zero_extend(v[7..0], 16),
  }
  in

  match reg {
    PC    =>    { check_byte_access(v, X); PC_reg = v },
    SP    =>    SP_reg = v,
    SRCG1 => SRCG1_reg = v,
    CG2   =>   CG2_reg = v,
    R4    =>    R4_reg = v,
    R5    =>    R5_reg = v,
    R6    =>    R6_reg = v,
    R7    =>    R7_reg = v,
    R8    =>    R8_reg = v,
    R9    =>    R9_reg = v,
    R10   =>   R10_reg = v,
    R11   =>   R11_reg = v,
    R12   =>   R12_reg = v,
    R13   =>   R13_reg = v,
    R14   =>   R14_reg = v,
    R15   =>   R15_reg = v,
  }
}

overload Xreg = {readReg, writeReg}

/*
Todo: separate out the constant generators => readability (maybe)
*/

val read: (BW, Register, AM) -> WordByte
val write: (BW, Register, AM, WordByte) -> unit


function read(bw, reg, am) = match (bw, reg, am) {

  /////////////////
  //Register mode//
  /////////////////

  (BYTE_INSTRUCTION, SRCG1, REGISTER_MODE) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=47
    //3.2.3 Status Register (SR)
    throw(notAllowed("Status register can not be read by byte operations"))
  },

  (bw, CG2, REGISTER_MODE) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=47
    //3.2.4 Constant Generator Registers CG1 and CG2
    match bw {
      WORD_INSTRUCTION => Word(0x0000),
      BYTE_INSTRUCTION => Byte(0x00)}
  },

  (bw, reg, REGISTER_MODE) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=50
    //3.3.1 Register Mode
    Xreg(bw, reg)
  },

  ////////////////
  //Indexed mode//
  ////////////////

  (bw, SRCG1, INDEXED_MODE) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=47
    //3.2.4 Constant Generator Registers CG1 and CG2
    LastInstructionFetch = fetch();
    let Word(address) : WordByte = LastInstructionFetch in
      XmemInstruction(bw,address)
  },

  (bw, CG2, INDEXED_MODE) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=47
    //3.2.4 Constant Generator Registers CG1 and CG2
    match bw {
      WORD_INSTRUCTION => Word(0x0001),
      BYTE_INSTRUCTION => Byte(0x01)}
  },

  (bw, reg, INDEXED_MODE) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=51
    //3.3.2 Indexed Mode
    let Word(initialAddress) : WordByte = read(WORD_INSTRUCTION,reg,REGISTER_MODE) in {
      LastInstructionFetch = fetch();
      let Word(addinigAddress) : WordByte = LastInstructionFetch in
      XmemInstruction(bw,initialAddress + addinigAddress)
    }
  },

  //////////////////////////
  //Indirect register mode//
  //////////////////////////

  (bw, SRCG1, INDIRECT_REGISTER_MODE) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=47
    //3.2.4 Constant Generator Registers CG1 and CG2
    match bw {
      WORD_INSTRUCTION => Word(0x0004),
      BYTE_INSTRUCTION => Byte(0x04)}
  },

  (bw, CG2, INDIRECT_REGISTER_MODE) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=47
    //3.2.4 Constant Generator Registers CG1 and CG2
    match bw {
      WORD_INSTRUCTION => Word(0x0002),
      BYTE_INSTRUCTION => Byte(0x02)}
  },

  (bw, reg, INDIRECT_REGISTER_MODE) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=54
    //3.3.5 Indirect Register Mode
    let Word(address) : WordByte = read(WORD_INSTRUCTION,reg,REGISTER_MODE) in
      XmemInstruction(bw,address)
  },

  ///////////////////////////////
  //Indirect Autoincrement Mode//
  ///////////////////////////////

  (bw, SRCG1, INDIRECT_AUTOINCREMENT_MODE) => {match bw {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=47
    //3.2.4 Constant Generator Registers CG1 and CG2
      WORD_INSTRUCTION => Word(0x0008),
      BYTE_INSTRUCTION => Byte(0x08)
    }
  },

  (bw, CG2, INDIRECT_AUTOINCREMENT_MODE) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=47
    //3.2.4 Constant Generator Registers CG1 and CG2
    match bw {
      WORD_INSTRUCTION => Word(0xFFFF),
      BYTE_INSTRUCTION => Byte(0xFF)
    }
  },

  (bw, reg, INDIRECT_AUTOINCREMENT_MODE) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=55
    //3.3.6 Indirect Autoincrement Mode
    let incVal:bits(16) = match bw {
      WORD_INSTRUCTION => 0x0002,
      BYTE_INSTRUCTION => 0x0001
    };
    let Word(address) : WordByte = read(WORD_INSTRUCTION,reg,REGISTER_MODE) in {
      write(WORD_INSTRUCTION,reg,REGISTER_MODE,Word(address + incVal));
      XmemInstruction(bw,address)
    }
  },
}

function write(bw, reg, am, v) = match (bw, reg, am, v) {

  /////////////////
  //Register mode//
  /////////////////

  (BYTE_INSTRUCTION, SRCG1, REGISTER_MODE, _) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=48
    //3.2.4 Constant Generator Registers CG1 and CG2
    throw(notAllowed("Status register can not be writen by byte operations"))
  },


  (bw, SRCG1, INDEXED_MODE, value) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=48
    //3.2.4 Constant Generator Registers CG1 and CG2
    let Word(address) : WordByte = LastInstructionFetch in
      XmemInstruction(bw,address) = value
  },

  (bw, CG2 ,_ ,_) => {
    //texas msp430 specification document page 48????
    //Todo: See if this happens in real code
    //ex: writing the reserved bits
    //throw(undefindedBehavior("CG2 can not do write operations"))
    //TODO: this is a "problem" since it is ued by NOP instructions
    Xreg(bw,CG2) = Xreg(bw,CG2)
  },

  (bw, reg, REGISTER_MODE, value) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=50
    //3.3.1 Register Mode
    Xreg(bw,reg) = value
  },

  ////////////////
  //Indexed mode//
  ////////////////

  (bw, reg, INDEXED_MODE, value) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=51
    //3.3.2 Indexed Mode
    let Word(address) : WordByte = read(WORD_INSTRUCTION,reg,REGISTER_MODE) + LastInstructionFetch in {
      XmemInstruction(bw,address) = value}
  },

  (bw, reg, _, value) => {
    //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=49
    //3.3 Addressing Modes
    throw(notAllowed("there should be no way in the specification to write in indirect register, or absolute mode"))
  },
}

overload X = {read, write}