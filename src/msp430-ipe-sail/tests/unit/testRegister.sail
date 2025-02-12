val constantGeneratorTest : (unit) -> unit
function constantGeneratorTest() = {
    assert(X(WORD_INSTRUCTION, SRCG1, INDEXED_MODE) == Word(0x0000));
    assert(X(WORD_INSTRUCTION, SRCG1, INDIRECT_REGISTER_MODE) == Word(0x0004));
    assert(X(WORD_INSTRUCTION, SRCG1, INDIRECT_AUTOINCREMENT_MODE) == Word(0x0008));
    assert(X(WORD_INSTRUCTION, CG2, REGISTER_MODE) == Word(0x0000));
    assert(X(WORD_INSTRUCTION, CG2, INDEXED_MODE) == Word(0x0001));
    assert(X(WORD_INSTRUCTION, CG2, INDIRECT_REGISTER_MODE) == Word(0x0002));
    assert(X(WORD_INSTRUCTION, CG2, INDIRECT_AUTOINCREMENT_MODE) == Word(0xFFFF));
    print_endline("constant generators for words produce the correct results");
    assert(X(BYTE_INSTRUCTION, SRCG1, INDEXED_MODE) == Byte(0x00));
    assert(X(BYTE_INSTRUCTION, SRCG1, INDIRECT_REGISTER_MODE) == Byte(0x04));
    assert(X(BYTE_INSTRUCTION, SRCG1, INDIRECT_AUTOINCREMENT_MODE) == Byte(0x08));
    assert(X(BYTE_INSTRUCTION, CG2, REGISTER_MODE) == Byte(0x00));
    assert(X(BYTE_INSTRUCTION, CG2, INDEXED_MODE) == Byte(0x01));
    assert(X(BYTE_INSTRUCTION, CG2, INDIRECT_REGISTER_MODE) == Byte(0x02));
    assert(X(BYTE_INSTRUCTION, CG2, INDIRECT_AUTOINCREMENT_MODE) == Byte(0xFF));
    print_endline("constant generators for bytes produce the correct results");
}

val readRegisterModeTest : (unit) -> unit
function readRegisterModeTest() = {
       PC_reg  = 0x1233;
       SP_reg  = 0x1235;
    SRCG1_reg  = 0x1236;
      CG2_reg  = 0x1237;
       R4_reg  = 0x1238;
       R5_reg  = 0x1239;
       R6_reg  = 0x123a;
       R7_reg  = 0x123b;
       R8_reg  = 0x123c;
       R9_reg  = 0x123d;
      R10_reg  = 0x123e;
      R11_reg  = 0x123f;
      R12_reg  = 0x1240;
      R13_reg  = 0x1241;
      R14_reg  = 0x1242;
      R15_reg  = 0x1243;

    assert(X(WORD_INSTRUCTION, PC,    REGISTER_MODE) == Word(0x1233));
    assert(X(WORD_INSTRUCTION, SP,    REGISTER_MODE) == Word(0x1235));
    assert(X(WORD_INSTRUCTION, SRCG1, REGISTER_MODE) == Word(0x1236));
    //CG2 is a constant generator in this mode
    assert(X(WORD_INSTRUCTION, R4,    REGISTER_MODE) == Word(0x1238));
    assert(X(WORD_INSTRUCTION, R5,    REGISTER_MODE) == Word(0x1239));
    assert(X(WORD_INSTRUCTION, R6,    REGISTER_MODE) == Word(0x123a));
    assert(X(WORD_INSTRUCTION, R7,    REGISTER_MODE) == Word(0x123b));
    assert(X(WORD_INSTRUCTION, R8,    REGISTER_MODE) == Word(0x123c));
    assert(X(WORD_INSTRUCTION, R9,    REGISTER_MODE) == Word(0x123d));
    assert(X(WORD_INSTRUCTION, R10,   REGISTER_MODE) == Word(0x123e));
    assert(X(WORD_INSTRUCTION, R11,   REGISTER_MODE) == Word(0x123f));
    assert(X(WORD_INSTRUCTION, R12,   REGISTER_MODE) == Word(0x1240));
    assert(X(WORD_INSTRUCTION, R13,   REGISTER_MODE) == Word(0x1241));
    assert(X(WORD_INSTRUCTION, R14,   REGISTER_MODE) == Word(0x1242));
    assert(X(WORD_INSTRUCTION, R15,   REGISTER_MODE) == Word(0x1243));
    print_endline("reding in register mode for Word instructions generates correct results");

    assert(X(BYTE_INSTRUCTION, PC,    REGISTER_MODE) == Byte(0x33));
    assert(X(BYTE_INSTRUCTION, SP,    REGISTER_MODE) == Byte(0x35));
    //SRCG1 is not allowed to be read by byte instrucions
    //CG2 is a constant generator in this mode
    assert(X(BYTE_INSTRUCTION, R4,    REGISTER_MODE) == Byte(0x38));
    assert(X(BYTE_INSTRUCTION, R5,    REGISTER_MODE) == Byte(0x39));
    assert(X(BYTE_INSTRUCTION, R6,    REGISTER_MODE) == Byte(0x3a));
    assert(X(BYTE_INSTRUCTION, R7,    REGISTER_MODE) == Byte(0x3b));
    assert(X(BYTE_INSTRUCTION, R8,    REGISTER_MODE) == Byte(0x3c));
    assert(X(BYTE_INSTRUCTION, R9,    REGISTER_MODE) == Byte(0x3d));
    assert(X(BYTE_INSTRUCTION, R10,   REGISTER_MODE) == Byte(0x3e));
    assert(X(BYTE_INSTRUCTION, R11,   REGISTER_MODE) == Byte(0x3f));
    assert(X(BYTE_INSTRUCTION, R12,   REGISTER_MODE) == Byte(0x40));
    assert(X(BYTE_INSTRUCTION, R13,   REGISTER_MODE) == Byte(0x41));
    assert(X(BYTE_INSTRUCTION, R14,   REGISTER_MODE) == Byte(0x42));
    assert(X(BYTE_INSTRUCTION, R15,   REGISTER_MODE) == Byte(0x43));
    print_endline("reding in register mode for Byte instructions generates correct results");
}

val writeRegisterModeTest : (unit) -> unit
function writeRegisterModeTest() = {
       PC_reg  = 0x0000;
       SP_reg  = 0x0000;
    SRCG1_reg  = 0x0000;
      CG2_reg  = 0x0000;
       R4_reg  = 0x0000;
       R5_reg  = 0x0000;
       R6_reg  = 0x0000;
       R7_reg  = 0x0000;
       R8_reg  = 0x0000;
       R9_reg  = 0x0000;
      R10_reg  = 0x0000;
      R11_reg  = 0x0000;
      R12_reg  = 0x0000;
      R13_reg  = 0x0000;
      R14_reg  = 0x0000;
      R15_reg  = 0x0000;

    X(WORD_INSTRUCTION, PC,    REGISTER_MODE) = Word(0x1233);
    X(WORD_INSTRUCTION, SP,    REGISTER_MODE) = Byte(0x35);
    X(WORD_INSTRUCTION, SRCG1, REGISTER_MODE) = Word(0x1236);
    //can not write to CG2
    X(WORD_INSTRUCTION, R4,    REGISTER_MODE) = Word(0x1238);
    X(WORD_INSTRUCTION, R5,    REGISTER_MODE) = Byte(0x39);
    X(WORD_INSTRUCTION, R6,    REGISTER_MODE) = Word(0x123a);
    X(WORD_INSTRUCTION, R7,    REGISTER_MODE) = Byte(0x3b);
    X(WORD_INSTRUCTION, R8,    REGISTER_MODE) = Word(0x123c);
    X(WORD_INSTRUCTION, R9,    REGISTER_MODE) = Byte(0x3d);
    X(WORD_INSTRUCTION, R10,   REGISTER_MODE) = Word(0x123e);
    X(WORD_INSTRUCTION, R11,   REGISTER_MODE) = Byte(0x3f);
    X(WORD_INSTRUCTION, R12,   REGISTER_MODE) = Word(0x1240);
    X(WORD_INSTRUCTION, R13,   REGISTER_MODE) = Byte(0x41);
    X(WORD_INSTRUCTION, R14,   REGISTER_MODE) = Word(0x1242);
    X(WORD_INSTRUCTION, R15,   REGISTER_MODE) = Byte(0x43);


    assert(X(WORD_INSTRUCTION, PC,    REGISTER_MODE) == Word(0x1233));
    assert(X(WORD_INSTRUCTION, SP,    REGISTER_MODE) == Word(0x0035));
    assert(X(WORD_INSTRUCTION, SRCG1, REGISTER_MODE) == Word(0x1236));
    assert(X(WORD_INSTRUCTION, R4,    REGISTER_MODE) == Word(0x1238));
    assert(X(WORD_INSTRUCTION, R5,    REGISTER_MODE) == Word(0x0039));
    assert(X(WORD_INSTRUCTION, R6,    REGISTER_MODE) == Word(0x123a));
    assert(X(WORD_INSTRUCTION, R7,    REGISTER_MODE) == Word(0x003b));
    assert(X(WORD_INSTRUCTION, R8,    REGISTER_MODE) == Word(0x123c));
    assert(X(WORD_INSTRUCTION, R9,    REGISTER_MODE) == Word(0x003d));
    assert(X(WORD_INSTRUCTION, R10,   REGISTER_MODE) == Word(0x123e));
    assert(X(WORD_INSTRUCTION, R11,   REGISTER_MODE) == Word(0x003f));
    assert(X(WORD_INSTRUCTION, R12,   REGISTER_MODE) == Word(0x1240));
    assert(X(WORD_INSTRUCTION, R13,   REGISTER_MODE) == Word(0x0041));
    assert(X(WORD_INSTRUCTION, R14,   REGISTER_MODE) == Word(0x1242));
    assert(X(WORD_INSTRUCTION, R15,   REGISTER_MODE) == Word(0x0043));
    print_endline("writing in register mode for Word instructions generates correct results");

       PC_reg  = 0x0000;
       SP_reg  = 0x0000;
    SRCG1_reg  = 0x0000;
      CG2_reg  = 0x0000;
       R4_reg  = 0x0000;
       R5_reg  = 0x0000;
       R6_reg  = 0x0000;
       R7_reg  = 0x0000;
       R8_reg  = 0x0000;
       R9_reg  = 0x0000;
      R10_reg  = 0x0000;
      R11_reg  = 0x0000;
      R12_reg  = 0x0000;
      R13_reg  = 0x0000;
      R14_reg  = 0x0000;
      R15_reg  = 0x0000;

    X(BYTE_INSTRUCTION, PC,    REGISTER_MODE) = Byte(0x33);
    X(BYTE_INSTRUCTION, SP,    REGISTER_MODE) = Word(0x1235);
    //can not write byte instructions to SRCG1
    //can not write to CG2
    X(BYTE_INSTRUCTION, R4,    REGISTER_MODE) = Byte(0x38);
    X(BYTE_INSTRUCTION, R5,    REGISTER_MODE) = Word(0x1239);
    X(BYTE_INSTRUCTION, R6,    REGISTER_MODE) = Byte(0x3a);
    X(BYTE_INSTRUCTION, R7,    REGISTER_MODE) = Word(0x123b);
    X(BYTE_INSTRUCTION, R8,    REGISTER_MODE) = Byte(0x3c);
    X(BYTE_INSTRUCTION, R9,    REGISTER_MODE) = Word(0x123d);
    X(BYTE_INSTRUCTION, R10,   REGISTER_MODE) = Byte(0x3e);
    X(BYTE_INSTRUCTION, R11,   REGISTER_MODE) = Word(0x123f);
    X(BYTE_INSTRUCTION, R12,   REGISTER_MODE) = Byte(0x40);
    X(BYTE_INSTRUCTION, R13,   REGISTER_MODE) = Word(0x1241);
    X(BYTE_INSTRUCTION, R14,   REGISTER_MODE) = Byte(0x42);
    X(BYTE_INSTRUCTION, R15,   REGISTER_MODE) = Word(0x1243);


    assert(X(WORD_INSTRUCTION, PC,    REGISTER_MODE) == Word(0x0033));
    assert(X(WORD_INSTRUCTION, SP,    REGISTER_MODE) == Word(0x0035));
    assert(X(WORD_INSTRUCTION, R4,    REGISTER_MODE) == Word(0x0038));
    assert(X(WORD_INSTRUCTION, R5,    REGISTER_MODE) == Word(0x0039));
    assert(X(WORD_INSTRUCTION, R6,    REGISTER_MODE) == Word(0x003a));
    assert(X(WORD_INSTRUCTION, R7,    REGISTER_MODE) == Word(0x003b));
    assert(X(WORD_INSTRUCTION, R8,    REGISTER_MODE) == Word(0x003c));
    assert(X(WORD_INSTRUCTION, R9,    REGISTER_MODE) == Word(0x003d));
    assert(X(WORD_INSTRUCTION, R10,   REGISTER_MODE) == Word(0x003e));
    assert(X(WORD_INSTRUCTION, R11,   REGISTER_MODE) == Word(0x003f));
    assert(X(WORD_INSTRUCTION, R12,   REGISTER_MODE) == Word(0x0040));
    assert(X(WORD_INSTRUCTION, R13,   REGISTER_MODE) == Word(0x0041));
    assert(X(WORD_INSTRUCTION, R14,   REGISTER_MODE) == Word(0x0042));
    assert(X(WORD_INSTRUCTION, R15,   REGISTER_MODE) == Word(0x0043));
    print_endline("reding in register mode for Byte instructions generates correct results");
}

val readIndexedModeTest : (unit) -> unit
function readIndexedModeTest() = {
    PC_reg  = 0x0500;
    R4_reg  = 0x1000;
    let offset = 0x0006 in {
      Xmem(WORD_INSTRUCTION,R4_reg) = Word(0x1233);
      Xmem(WORD_INSTRUCTION,R4_reg + offset) = Word(0x1235);
      Xmem(WORD_INSTRUCTION,PC_reg) = Word(0x0000);
      Xmem(WORD_INSTRUCTION,PC_reg + 0x0002) = Word(offset);
      Xmem(WORD_INSTRUCTION,PC_reg + 0x0004) = Word(offset);
      Xmem(WORD_INSTRUCTION,PC_reg + 0x0004 + offset) = Word(0x1236);
      assert(X(WORD_INSTRUCTION, R4,    INDEXED_MODE) == Word(0x1233));
      assert(X(WORD_INSTRUCTION, R4,    INDEXED_MODE) == Word(0x1235));
      assert(X(WORD_INSTRUCTION, PC,    INDEXED_MODE) == Word(0x1236));


      //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=51
      R5_reg  = 0x1080;
      Xmem(WORD_INSTRUCTION,0x1082) = Word(0x1234);
      PC_reg  = 0xFF14;
      Xmem(WORD_INSTRUCTION,0xFF14) = Word(0x0002);
      assert(X(WORD_INSTRUCTION, R5,    INDEXED_MODE) == Word(0x1234));



      //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=52
      Xmem(WORD_INSTRUCTION,0xFF14) = Word(0xF102);
      Xmem(WORD_INSTRUCTION,0xF016) = Word(0xA123);
      PC_reg  = 0xFF14;
      assert(X(WORD_INSTRUCTION, PC,    INDEXED_MODE) == Word(0xA123));

      //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=53
      Xmem(WORD_INSTRUCTION,0xFF14) = Word(0xF016);
      Xmem(WORD_INSTRUCTION,0xF016) = Word(0xA123);
      PC_reg  = 0xFF14;
      assert(X(WORD_INSTRUCTION, SRCG1,    INDEXED_MODE) == Word(0xA123));

      print_endline("reading in indexed mode for Word instructions generates correct results");

      //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=51
      R5_reg  = 0x1080;
      Xmem(WORD_INSTRUCTION,0x1082) = Word(0x1234);
      PC_reg  = 0xFF14;
      Xmem(WORD_INSTRUCTION,0xFF14) = Word(0x0002);
      assert(X(BYTE_INSTRUCTION, R5,    INDEXED_MODE) == Byte(0x34));



      //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=52
      Xmem(WORD_INSTRUCTION,0xFF14) = Word(0xF102);
      Xmem(WORD_INSTRUCTION,0xF016) = Word(0xA123);
      PC_reg  = 0xFF14;
      assert(X(BYTE_INSTRUCTION, PC,    INDEXED_MODE) == Byte(0x23));

      //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=53
      Xmem(WORD_INSTRUCTION,0xFF14) = Word(0xF016);
      Xmem(WORD_INSTRUCTION,0xF016) = Word(0xA123);
      PC_reg  = 0xFF14;
      assert(X(BYTE_INSTRUCTION, SRCG1,    INDEXED_MODE) == Byte(0x23));
      
      print_endline("reading in indexed mode for Byte instructions generates correct results");
    }
}
val writeIndexedModeTest : (unit) -> unit
function writeIndexedModeTest() = {
  //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=51
  R5_reg  = 0x1080;
  Xmem(WORD_INSTRUCTION,0x1082) = Word(0x1234);
  PC_reg  = 0xFF14;
  Xmem(WORD_INSTRUCTION,0xFF14) = Word(0x0002);
  //need read to set the last read value
  assert(X(WORD_INSTRUCTION, R5,    INDEXED_MODE) == Word(0x1234));

  X(WORD_INSTRUCTION, R5,    INDEXED_MODE) = Word(0x1236);
  assert(Xmem(WORD_INSTRUCTION,0x1082) == Word(0x1236));

  //https://www.ti.com/lit/ug/slau144k/slau144k.pdf#page=51
  R5_reg  = 0x1080;
  Xmem(WORD_INSTRUCTION,0x1082) = Word(0x1234);
  PC_reg  = 0xFF14;
  Xmem(WORD_INSTRUCTION,0xFF14) = Word(0x0002);
  //need read to set the last read value
  assert(X(WORD_INSTRUCTION, R5,    INDEXED_MODE) == Word(0x1234));

  X(BYTE_INSTRUCTION, R5,    INDEXED_MODE) = Word(0x5636);
  printWordByte("a",Xmem(WORD_INSTRUCTION,0x1082));
  assert(Xmem(WORD_INSTRUCTION,0x1082) == Word(0x1236));
}

val testRegister : (unit) -> unit
function testRegister() = {

  print_endline("------------------------------------------------------------");
  print_endline("------------------ register testing ------------------------");
  print_endline("------------------------------------------------------------");

  print_endline("1) testing the constant generators");
  constantGeneratorTest();
  print_endline("2) testing reading");
  print_endline("2.1) register mode");
  readRegisterModeTest();
  print_endline("2.2) indexed mode");
  readIndexedModeTest();
  print_endline("2.3) indirect register mode");
  print_endline("!!!! not yet implemented");
  print_endline("2.4) indirect autoincrement mode");
  print_endline("!!!! not yet implemented");

  print_endline("3) testing writing");
  print_endline("3.1) register mode");
  writeRegisterModeTest();
  print_endline("3.2) indexed mode");
  writeIndexedModeTest()
}