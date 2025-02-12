val testStatusbits : (unit) -> unit
function testStatusbits() = {

  print_endline("------------------------------------------------------------");
  print_endline("------------------ status bit testing ----------------------");
  print_endline("------------------------------------------------------------");

  SRCG1_reg = 0x0000;
  setAllStatusbits();
  assert(getCarryBit() == 0b1,"setAllStatusbits() does not work");
  assert(getOverflowBit() == 0b1,"setAllStatusbits() does not work");
  assert(getNegativeBit() == 0b1,"setAllStatusbits() does not work");
  assert(getZeroBit() == 0b1,"setAllStatusbits() does not work");
  clearStatusRegisters();
  assert(getCarryBit() == 0b0,"clearStatusRegisters() does not work");
  assert(getOverflowBit() == 0b0,"clearStatusRegisters() does not work");
  assert(getNegativeBit() == 0b0,"clearStatusRegisters() does not work");
  assert(getZeroBit() == 0b0,"clearStatusRegisters() does not work");

  print_endline("Group status bit manipulation works");

  setCarrybit();
  assert(getCarryBit() == 0b1    ,"setCarrybit() does not set the carrybit" );
  assert(getOverflowBit() == 0b0 ,"setCarrybit() changes the wrong bit");
  assert(getNegativeBit() == 0b0 ,"setCarrybit() changes the wrong bit");
  assert(getZeroBit() == 0b0     ,"setCarrybit() changes the wrong bit");
  clearCarrybit();
  assert(getCarryBit() == 0b0    ,"clearCarrybit(); does not set the carrybit" );
  assert(getOverflowBit() == 0b0 ,"clearCarrybit(); changes the wrong bit");
  assert(getNegativeBit() == 0b0 ,"clearCarrybit(); changes the wrong bit");
  assert(getZeroBit() == 0b0     ,"clearCarrybit(); changes the wrong bit");
  setCarrybit(0b1);
  assert(getCarryBit() == 0b1    ,"setCarrybit(0b1); does not set the carrybit" );
  assert(getOverflowBit() == 0b0 ,"setCarrybit(0b1); changes the wrong bit");
  assert(getNegativeBit() == 0b0 ,"setCarrybit(0b1); changes the wrong bit");
  assert(getZeroBit() == 0b0     ,"setCarrybit(0b1); changes the wrong bit");
  setCarrybit(0b0);
  assert(getCarryBit() == 0b0    ,"setCarrybit() does not set the carrybit" );
  assert(getOverflowBit() == 0b0 ,"setCarrybit() changes the wrong bit");
  assert(getNegativeBit() == 0b0 ,"setCarrybit() changes the wrong bit");
  assert(getZeroBit() == 0b0     ,"setCarrybit() changes the wrong bit");

  print_endline("Carrybit manipulation works");


  setOverflowbit();
  assert(getOverflowBit() == 0b1    ,"setOverflowbit() does not set the overflowbit" );
  assert(getCarryBit() == 0b0       ,"setOverflowbit() changes the wrong bit");
  assert(getNegativeBit() == 0b0    ,"setOverflowbit() changes the wrong bit");
  assert(getZeroBit() == 0b0        ,"setOverflowbit() changes the wrong bit");
  clearOverflowbit();
  assert(getOverflowBit() == 0b0    ,"clearOverflowbit(); does not set the overflowbit" );
  assert(getCarryBit() == 0b0       ,"clearOverflowbit(); changes the wrong bit");
  assert(getNegativeBit() == 0b0    ,"clearOverflowbit(); changes the wrong bit");
  assert(getZeroBit() == 0b0        ,"clearOverflowbit(); changes the wrong bit");
  setOverflowbit(0b1);
  assert(getOverflowBit() == 0b1    ,"setOverflowbit(0b1); does not set the overflowbit" );
  assert(getCarryBit() == 0b0       ,"setOverflowbit(0b1); changes the wrong bit");
  assert(getNegativeBit() == 0b0    ,"setOverflowbit(0b1); changes the wrong bit");
  assert(getZeroBit() == 0b0        ,"setOverflowbit(0b1); changes the wrong bit");
  setOverflowbit(0b0);
  assert(getOverflowBit() == 0b0    ,"setOverflowbit(0b0); does not set the overflowbit" );
  assert(getCarryBit() == 0b0       ,"setOverflowbit(0b0); changes the wrong bit");
  assert(getNegativeBit() == 0b0    ,"setOverflowbit(0b0); changes the wrong bit");
  assert(getZeroBit() == 0b0        ,"setOverflowbit(0b0); changes the wrong bit");

  print_endline("Overflowbit manipulation works");
  
  setNegativebit();
  assert(getNegativeBit() == 0b1    ,"setNegativebit() does not set the negativebit" );
  assert(getCarryBit() == 0b0       ,"setNegativebit() changes the wrong bit");
  assert(getOverflowBit() == 0b0    ,"setNegativebit() changes the wrong bit");
  assert(getZeroBit() == 0b0        ,"setNegativebit() changes the wrong bit");
  clearNegativebit();
  assert(getNegativeBit() == 0b0    ,"clearNegativebit(); does not set the negativebit" );
  assert(getCarryBit() == 0b0       ,"clearNegativebit(); changes the wrong bit");
  assert(getOverflowBit() == 0b0    ,"clearNegativebit(); changes the wrong bit");
  assert(getZeroBit() == 0b0        ,"clearNegativebit(); changes the wrong bit");
  setNegativebit(0b1);
  assert(getNegativeBit() == 0b1    ,"setNegativebit(0b1); does not set the negativebit" );
  assert(getCarryBit() == 0b0       ,"setNegativebit(0b1); changes the wrong bit");
  assert(getOverflowBit() == 0b0    ,"setNegativebit(0b1); changes the wrong bit");
  assert(getZeroBit() == 0b0        ,"setNegativebit(0b1); changes the wrong bit");
  setNegativebit(0b0);
  assert(getNegativeBit() == 0b0    ,"setNegativebit(0b0); does not set the negativebit" );
  assert(getCarryBit() == 0b0       ,"setNegativebit(0b0); changes the wrong bit");
  assert(getOverflowBit() == 0b0    ,"setNegativebit(0b0); changes the wrong bit");
  assert(getZeroBit() == 0b0        ,"setNegativebit(0b0); changes the wrong bit");

  print_endline("Negativebit manipulation works");


  setZerobit();
  assert(getZeroBit() == 0b1        ,"setZerobit() does not set the zerobit" );
  assert(getCarryBit() == 0b0       ,"setZerobit() changes the wrong bit");
  assert(getOverflowBit() == 0b0    ,"setZerobit() changes the wrong bit");
  assert(getNegativeBit() == 0b0    ,"setZerobit() changes the wrong bit");
  clearZerobit();
  assert(getZeroBit() == 0b0        ,"clearZerobit(); does not set the zerobit" );
  assert(getCarryBit() == 0b0       ,"clearZerobit(); changes the wrong bit");
  assert(getOverflowBit() == 0b0    ,"clearZerobit(); changes the wrong bit");
  assert(getNegativeBit() == 0b0    ,"clearZerobit(); changes the wrong bit");
  setZerobit(0b1);
  assert(getZeroBit() == 0b1        ,"setZerobit(0b1); does not set the zerobit" );
  assert(getCarryBit() == 0b0       ,"setZerobit(0b1); changes the wrong bit");
  assert(getOverflowBit() == 0b0    ,"setZerobit(0b1); changes the wrong bit");
  assert(getNegativeBit() == 0b0    ,"setZerobit(0b1); changes the wrong bit");
  setZerobit(0b0);
  assert(getZeroBit() == 0b0        ,"setZerobit(0b0); does not set the zerobit" );
  assert(getCarryBit() == 0b0       ,"setZerobit(0b0); changes the wrong bit");
  assert(getOverflowBit() == 0b0    ,"setZerobit(0b0); changes the wrong bit");
  assert(getNegativeBit() == 0b0    ,"setZerobit(0b0); changes the wrong bit");

  print_endline("Zerobit manipulation works");

  assert(SRCG1_reg == 0x0000, "status bit manipulation changes values that it should not");
  print_endline("statusbit manipulation does not have unexpected side effects");
}