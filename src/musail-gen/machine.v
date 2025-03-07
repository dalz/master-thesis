Require Export base.

From Coq Require Import Lists.List
                        Classes.EquivDec
                        Strings.String
                        ZArith.BinInt.

From Katamaran Require Import Semantics.Registers
                              Bitvector
                              Program.

From stdpp Require Import finite.

From Equations Require Import Equations.

Import ctx.notations
       ctx.resolution
       env.notations
       bv.notations
       ListNotations.

Local Open Scope string_scope.
Local Open Scope list_scope.

Import UntitledBase.

Module Import ModelProgram <: Program UntitledBase.
  Section FunDeclKit.
    Inductive Fun : PCtx -> Ty -> Set :=
      (* Foreign or undefined functions. This should be moved at some point.  *)
      | read_ram : Fun [ "" ∷ ty.int; "" ∷ ty.int; "addr" ∷ ty.Address; "" ∷ ty.Address ] ty.byteBits
      | write_ram : Fun [ "" ∷ ty.int; "" ∷ ty.int; "addr" ∷ ty.Address; "" ∷ ty.Address; "" ∷ ty.byteBits ] ty.unit
      | shiftl {m} : Fun [ "x" ∷ ty.bvec m; "y" ∷ ty.int ] (ty.bvec m)
      | shiftr {m} : Fun [ "x" ∷ ty.bvec m; "y" ∷ ty.int ] (ty.bvec m)
      | concat_str : Fun [ "x" ∷ ty.string; "y" ∷ ty.string ] ty.string
      | bits_str : Fun [ "x" ∷ ty.Address ] ty.string
      | emod_int : Fun [ "x" ∷ ty.int; "y" ∷ ty.int ] ty.int
      | undefined_bitvector {n} : Fun [ "x" ∷ ty.int ] (ty.bvec n)

      | neg_vec4                             : Fun[
                                                    "v"  ∷  ty.bvec (4)
                                                  ](ty.bvec (4))
      | bitmaping_forwards                   : Fun[
                                                    "arg#"  ∷  ty.enum Ebw
                                                  ](ty.bvec (1))
      | bitmaping_backwards                  : Fun[
                                                    "arg#"  ∷  ty.bvec (1)
                                                  ](ty.enum Ebw)
      | bitmaping_forwards_matches           : Fun[
                                                    "arg#"  ∷  ty.enum Ebw
                                                  ](ty.bool)
      | bitmaping_backwards_matches          : Fun[
                                                    "arg#"  ∷  ty.bvec (1)
                                                  ](ty.bool)
      | regName                              : Fun[
                                                    "reg"  ∷  ty.enum Eregister
                                                  ](ty.string)
      | AMstring                             : Fun[
                                                    "am"  ∷  ty.enum Eam
                                                  ](ty.string)
      | BWstring                             : Fun[
                                                    "bw"  ∷  ty.enum Ebw
                                                  ](ty.string)
      | BWSizeString                         : Fun[
                                                    "bw"  ∷  ty.enum Ebw
                                                  ](ty.string)
      | duopName                             : Fun[
                                                    "op"  ∷  ty.enum Edoubleop
                                                  ](ty.string)
      | singleopName                         : Fun[
                                                    "op"  ∷  ty.enum Esingleop
                                                  ](ty.string)
      | jumpName                             : Fun[
                                                    "op"  ∷  ty.enum Ejump
                                                  ](ty.string)
      | logWithVerbosity                     : Fun[
                                                    "n"  ∷  ty.int;
                                                    "s"  ∷  ty.string
                                                  ](ty.unit)
      | RegisterMapping_forwards             : Fun[
                                                    "arg#"  ∷  ty.enum Eregister
                                                  ](ty.bvec (4))
      | RegisterMapping_backwards            : Fun[
                                                    "arg#"  ∷  ty.bvec (4)
                                                  ](ty.enum Eregister)
      | RegisterMapping_forwards_matches     : Fun[
                                                    "arg#"  ∷  ty.enum Eregister
                                                  ](ty.bool)
      | RegisterMapping_backwards_matches    : Fun[
                                                    "arg#"  ∷  ty.bvec (4)
                                                  ](ty.bool)
      | init_base_regs                       : Fun[
                                                    "_ж145"  ∷  ty.unit
                                                  ](ty.unit)
      | toByte                               : Fun[
                                                    "merge#var"  ∷  ty.union Uwordbyte
                                                  ](ty.union Uwordbyte)
      | signedWb                             : Fun[
                                                    "merge#var"  ∷  ty.union Uwordbyte
                                                  ](ty.int)
      | unsignedWb                           : Fun[
                                                    "merge#var"  ∷  ty.union Uwordbyte
                                                  ](ty.int)
      | addBw                                : Fun[
                                                    "x"  ∷  ty.union Uwordbyte;
                                                    "y"  ∷  ty.union Uwordbyte
                                                  ](ty.union Uwordbyte)
      | zero_extend_bit_to_byte              : Fun[
                                                    "b"  ∷  ty.bvec (1)
                                                  ]((ty.union Uwordbyte))
      | not_wordByte                         : Fun[
                                                    "merge#var"  ∷  ty.union Uwordbyte
                                                  ](ty.union Uwordbyte)
      | and_wordByte                         : Fun[
                                                    "x"  ∷  ty.union Uwordbyte;
                                                    "y"  ∷  ty.union Uwordbyte
                                                  ](ty.union Uwordbyte)
      | or_wordByte                          : Fun[
                                                    "x"  ∷  ty.union Uwordbyte;
                                                    "y"  ∷  ty.union Uwordbyte
                                                  ](ty.union Uwordbyte)
      | xor_wordByte                         : Fun[
                                                    "x"  ∷  ty.union Uwordbyte;
                                                    "y"  ∷  ty.union Uwordbyte
                                                  ](ty.union Uwordbyte)
      | eq_wordByte                          : Fun[
                                                    "x"  ∷  ty.union Uwordbyte;
                                                    "y"  ∷  ty.union Uwordbyte
                                                  ](ty.bool)
      | xor_bool                             : Fun[
                                                    "b1"  ∷  ty.bool;
                                                    "b2"  ∷  ty.bool
                                                  ](ty.bool)
      | isNegative                           : Fun[
                                                    "w"  ∷  ty.union Uwordbyte
                                                  ](ty.bool)
      | isZero                               : Fun[
                                                    "w"  ∷  ty.union Uwordbyte
                                                  ](ty.bool)
      | printWordByte                        : Fun[
                                                    "s"  ∷  ty.string;
                                                    "wb"  ∷  ty.union Uwordbyte
                                                  ](ty.unit)
      | WordByteString                       : Fun[
                                                    "wb"  ∷  ty.union Uwordbyte
                                                  ](ty.string)
      | getOverflowBit                       : Fun[
                                                    "_ж409"  ∷  ty.unit
                                                  ](ty.bvec (1))
      | setOverflowbitBit                    : Fun[
                                                    "b"  ∷  ty.bvec (1)
                                                  ](ty.unit)
      | setOverflowbitTrue                   : Fun[
                                                    "_ж413"  ∷  ty.unit
                                                  ](ty.unit)
      | clearOverflowbit                     : Fun[
                                                    "_ж416"  ∷  ty.unit
                                                  ](ty.unit)
      | overflowbitSet                       : Fun[
                                                    "_ж419"  ∷  ty.unit
                                                  ](ty.bool)
      | getNegativeBit                       : Fun[
                                                    "_ж421"  ∷  ty.unit
                                                  ](ty.bvec (1))
      | setNegativebitBit                    : Fun[
                                                    "b"  ∷  ty.bvec (1)
                                                  ](ty.unit)
      | setNegativebitTrue                   : Fun[
                                                    "_ж425"  ∷  ty.unit
                                                  ](ty.unit)
      | clearNegativebit                     : Fun[
                                                    "_ж428"  ∷  ty.unit
                                                  ](ty.unit)
      | negativebitSet                       : Fun[
                                                    "_ж431"  ∷  ty.unit
                                                  ](ty.bool)
      | getZeroBit                           : Fun[
                                                    "_ж433"  ∷  ty.unit
                                                  ](ty.bvec (1))
      | setZerobitBit                        : Fun[
                                                    "b"  ∷  ty.bvec (1)
                                                  ](ty.unit)
      | setZerobitTrue                       : Fun[
                                                    "_ж437"  ∷  ty.unit
                                                  ](ty.unit)
      | clearZerobit                         : Fun[
                                                    "_ж440"  ∷  ty.unit
                                                  ](ty.unit)
      | zerobitSet                           : Fun[
                                                    "_ж443"  ∷  ty.unit
                                                  ](ty.bool)
      | getCarryBit                          : Fun[
                                                    "_ж445"  ∷  ty.unit
                                                  ](ty.bvec (1))
      | setCarrybitBit                       : Fun[
                                                    "b"  ∷  ty.bvec (1)
                                                  ](ty.unit)
      | setCarrybitTrue                      : Fun[
                                                    "_ж449"  ∷  ty.unit
                                                  ](ty.unit)
      | clearCarrybit                        : Fun[
                                                    "_ж452"  ∷  ty.unit
                                                  ](ty.unit)
      | carrybitSet                          : Fun[
                                                    "_ж455"  ∷  ty.unit
                                                  ](ty.bool)
      | setAllStatusbits                     : Fun[
                                                    "_ж457"  ∷  ty.unit
                                                  ](ty.unit)
      | clearStatusRegisters                 : Fun[
                                                    "_ж467"  ∷  ty.unit
                                                  ](ty.unit)
      | setResultStatusRegisters             : Fun[
                                                    "res"  ∷  ty.union Uwordbyte
                                                  ](ty.unit)
      | mpu_register_index_forwards          : Fun[
                                                    "arg#"  ∷  ty.enum Empu_register_name
                                                  ](ty.int)
      | mpu_register_index_backwards         : Fun[
                                                    "arg#"  ∷  ty.int
                                                  ](ty.enum Empu_register_name)
      | mpu_register_index_forwards_matches  : Fun[
                                                    "arg#"  ∷  ty.enum Empu_register_name
                                                  ](ty.bool)
      | mpu_register_index_backwards_matches : Fun[
                                                    "arg#"  ∷  ty.int
                                                  ](ty.bool)
      | is_mpu_reg_addr                      : Fun[
                                                    "addr"  ∷  ty.bvec (16)
                                                  ](ty.bool)
      | read_mpu_reg_byte                    : Fun[
                                                    "addr"  ∷  ty.bvec (16)
                                                  ](ty.bvec (8))
      | is_lockable_mpu_reg                  : Fun[
                                                    "reg"  ∷  ty.enum Empu_register_name
                                                  ](ty.bool)
      | is_ipe_reg                           : Fun[
                                                    "reg"  ∷  ty.enum Empu_register_name
                                                  ](ty.bool)
      | write_mpu_reg_byte                   : Fun[
                                                    "addr"  ∷  ty.bvec (16);
                                                    "v"  ∷  ty.bvec (8)
                                                  ](ty.unit)
      | ipe_lower                            : Fun[
                                                    "_ж640"  ∷  ty.unit
                                                  ](ty.int)
      | ipe_higher                           : Fun[
                                                    "_ж642"  ∷  ty.unit
                                                  ](ty.int)
      | in_ipe_segment                       : Fun[
                                                    "addr"  ∷  ty.bvec (16)
                                                  ](ty.bool)
      | in_ivt_or_rv                         : Fun[
                                                    "addr"  ∷  ty.bvec (16)
                                                  ](ty.bool)
      | is_x                                 : Fun[
                                                    "m"  ∷  ty.enum Eaccess_mode
                                                  ](ty.bool)
      | check_ipe_access                     : Fun[
                                                    "addr"  ∷  ty.bvec (16);
                                                    "m"  ∷  ty.enum Eaccess_mode
                                                  ](ty.bool)
      | check_byte_access                    : Fun[
                                                    "addr"  ∷  ty.bvec (16);
                                                    "m"  ∷  ty.enum Eaccess_mode
                                                  ](ty.unit)
      | read_mem_aux                         : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "addr"  ∷  ty.bvec (16);
                                                    "m"  ∷  ty.enum Eaccess_mode
                                                  ](ty.union Uwordbyte)
      | readMem                              : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "addr"  ∷  ty.bvec (16)
                                                  ](ty.union Uwordbyte)
      | writeMem                             : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "addr"  ∷  ty.bvec (16);
                                                    "v"  ∷  ty.union Uwordbyte
                                                  ](ty.unit)
      | readMemInstruction                   : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "address"  ∷  ty.bvec (16)
                                                  ](ty.union Uwordbyte)
      | writeMemInstruction                  : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "address"  ∷  ty.bvec (16);
                                                    "value"  ∷  ty.union Uwordbyte
                                                  ](ty.unit)
      | incPC                                : Fun[
                                                    "_ж713"  ∷  ty.unit
                                                  ](ty.unit)
      | fetch                                : Fun[
                                                    "_ж716"  ∷  ty.unit
                                                  ](ty.union Uwordbyte)
      | sourcemaping_forwards                : Fun[
                                                    "arg#"  ∷  ty.enum Eam
                                                  ](ty.bvec (2))
      | sourcemaping_backwards               : Fun[
                                                    "arg#"  ∷  ty.bvec (2)
                                                  ](ty.enum Eam)
      | sourcemaping_forwards_matches        : Fun[
                                                    "arg#"  ∷  ty.enum Eam
                                                  ](ty.bool)
      | sourcemaping_backwards_matches       : Fun[
                                                    "arg#"  ∷  ty.bvec (2)
                                                  ](ty.bool)
      | destinationmaping_forwards           : Fun[
                                                    "arg#"  ∷  ty.enum Eam
                                                  ](ty.bvec (1))
      | destinationmaping_backwards          : Fun[
                                                    "arg#"  ∷  ty.bvec (1)
                                                  ](ty.enum Eam)
      | destinationmaping_forwards_matches   : Fun[
                                                    "arg#"  ∷  ty.enum Eam
                                                  ](ty.bool)
      | destinationmaping_backwards_matches  : Fun[
                                                    "arg#"  ∷  ty.bvec (1)
                                                  ](ty.bool)
      | readReg                              : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "reg"  ∷  ty.enum Eregister
                                                  ](ty.union Uwordbyte)
      | writeReg                             : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "reg"  ∷  ty.enum Eregister;
                                                    "v"  ∷  ty.union Uwordbyte
                                                  ](ty.unit)
      | read                                 : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "reg"  ∷  ty.enum Eregister;
                                                    "am"  ∷  ty.enum Eam
                                                  ](ty.union Uwordbyte)
      | write                                : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "reg"  ∷  ty.enum Eregister;
                                                    "am"  ∷  ty.enum Eam;
                                                    "v"  ∷  ty.union Uwordbyte
                                                  ](ty.unit)
      | move_inst                            : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "sourceRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeSource"  ∷  ty.enum Eam;
                                                    "destinationRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeDestination"  ∷  ty.enum Eam
                                                  ](ty.unit)
      | hasCarry                             : Fun[
                                                    "w1"  ∷  ty.union Uwordbyte;
                                                    "w2"  ∷  ty.union Uwordbyte;
                                                    "res"  ∷  ty.union Uwordbyte
                                                  ](ty.bool)
      | hasOverflowAddition                  : Fun[
                                                    "w1"  ∷  ty.union Uwordbyte;
                                                    "w2"  ∷  ty.union Uwordbyte;
                                                    "res"  ∷  ty.union Uwordbyte
                                                  ](ty.bool)
      | addWithStatusRegister                : Fun[
                                                    "w1"  ∷  ty.union Uwordbyte;
                                                    "w2"  ∷  ty.union Uwordbyte
                                                  ](ty.union Uwordbyte)
      | add_inst                             : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "sourceRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeSource"  ∷  ty.enum Eam;
                                                    "destinationRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeDestination"  ∷  ty.enum Eam
                                                  ](ty.unit)
      | addc_inst                            : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "sourceRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeSource"  ∷  ty.enum Eam;
                                                    "destinationRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeDestination"  ∷  ty.enum Eam
                                                  ](ty.unit)
      | sub_inst                             : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "sourceRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeSource"  ∷  ty.enum Eam;
                                                    "destinationRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeDestination"  ∷  ty.enum Eam
                                                  ](ty.unit)
      | subc_inst                            : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "sourceRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeSource"  ∷  ty.enum Eam;
                                                    "destinationRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeDestination"  ∷  ty.enum Eam
                                                  ](ty.unit)
      | cmp_inst                             : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "sourceRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeSource"  ∷  ty.enum Eam;
                                                    "destinationRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeDestination"  ∷  ty.enum Eam
                                                  ](ty.unit)
      | andWithStatusRegister                : Fun[
                                                    "w1"  ∷  ty.union Uwordbyte;
                                                    "w2"  ∷  ty.union Uwordbyte
                                                  ](ty.union Uwordbyte)
      | and_inst                             : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "sourceRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeSource"  ∷  ty.enum Eam;
                                                    "destinationRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeDestination"  ∷  ty.enum Eam
                                                  ](ty.unit)
      | xorWithStatusRegister                : Fun[
                                                    "w1"  ∷  ty.union Uwordbyte;
                                                    "w2"  ∷  ty.union Uwordbyte
                                                  ](ty.union Uwordbyte)
      | xor_inst                             : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "sourceRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeSource"  ∷  ty.enum Eam;
                                                    "destinationRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeDestination"  ∷  ty.enum Eam
                                                  ](ty.unit)
      | bic_inst                             : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "sourceRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeSource"  ∷  ty.enum Eam;
                                                    "destinationRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeDestination"  ∷  ty.enum Eam
                                                  ](ty.unit)
      | bis_inst                             : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "sourceRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeSource"  ∷  ty.enum Eam;
                                                    "destinationRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeDestination"  ∷  ty.enum Eam
                                                  ](ty.unit)
      | bit_inst                             : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "sourceRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeSource"  ∷  ty.enum Eam;
                                                    "destinationRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeDestination"  ∷  ty.enum Eam
                                                  ](ty.unit)
      | asDecimal                            : Fun[
                                                    "merge#var"  ∷  ty.union Uwordbyte
                                                  ](ty.int)
      | asWordByte                           : Fun[
                                                    "number"  ∷  ty.int
                                                  ](ty.union Uwordbyte)
      | dadd_inst                            : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "sourceRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeSource"  ∷  ty.enum Eam;
                                                    "destinationRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeDestination"  ∷  ty.enum Eam
                                                  ](ty.unit)
      | encdec_doubleop_forwards             : Fun[
                                                    "arg#"  ∷  ty.enum Edoubleop
                                                  ](ty.bvec (4))
      | encdec_doubleop_backwards            : Fun[
                                                    "arg#"  ∷  ty.bvec (4)
                                                  ](ty.enum Edoubleop)
      | encdec_doubleop_forwards_matches     : Fun[
                                                    "arg#"  ∷  ty.enum Edoubleop
                                                  ](ty.bool)
      | encdec_doubleop_backwards_matches    : Fun[
                                                    "arg#"  ∷  ty.bvec (4)
                                                  ](ty.bool)
      | rrc_inst                             : Fun[
                                                    "merge#var"  ∷  ty.tuple [
                                                                                 ty.enum Ebw;
                                                                                 ty.enum Eam;
                                                                                 ty.enum Eregister
                                                                               ]
                                                  ](ty.unit)
      | rra_inst                             : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "am"  ∷  ty.enum Eam;
                                                    "reg"  ∷  ty.enum Eregister
                                                  ](ty.unit)
      | push_inst                            : Fun[
                                                    "bw"  ∷  ty.enum Ebw;
                                                    "addressingMode"  ∷  ty.enum Eam;
                                                    "reg"  ∷  ty.enum Eregister
                                                  ](ty.unit)
      | swpb_inst                            : Fun[
                                                    "_ж3947"  ∷  ty.enum Ebw;
                                                    "addressingMode"  ∷  ty.enum Eam;
                                                    "reg"  ∷  ty.enum Eregister
                                                  ](ty.unit)
      | call_inst                            : Fun[
                                                    "merge#var"  ∷  ty.tuple [
                                                                                 ty.enum Ebw;
                                                                                 ty.enum Eam;
                                                                                 ty.enum Eregister
                                                                               ]
                                                  ](ty.unit)
      | reti_inst                            : Fun[
                                                    "_ж3998"  ∷  ty.enum Ebw;
                                                    "_ж3999"  ∷  ty.enum Eam;
                                                    "_ж4000"  ∷  ty.enum Eregister
                                                  ](ty.unit)
      | sxt_inst                             : Fun[
                                                    "_ж4016"  ∷  ty.enum Ebw;
                                                    "addressingMode"  ∷  ty.enum Eam;
                                                    "reg"  ∷  ty.enum Eregister
                                                  ](ty.unit)
      | encdec_singleop_forwards             : Fun[
                                                    "arg#"  ∷  ty.enum Esingleop
                                                  ](ty.bvec (9))
      | encdec_singleop_backwards            : Fun[
                                                    "arg#"  ∷  ty.bvec (9)
                                                  ](ty.enum Esingleop)
      | encdec_singleop_forwards_matches     : Fun[
                                                    "arg#"  ∷  ty.enum Esingleop
                                                  ](ty.bool)
      | encdec_singleop_backwards_matches    : Fun[
                                                    "arg#"  ∷  ty.bvec (9)
                                                  ](ty.bool)
      | jeq_inst                             : Fun[
                                                    "offset"  ∷  ty.bvec (10)
                                                  ](ty.unit)
      | jne_inst                             : Fun[
                                                    "offset"  ∷  ty.bvec (10)
                                                  ](ty.unit)
      | jc_inst                              : Fun[
                                                    "offset"  ∷  ty.bvec (10)
                                                  ](ty.unit)
      | jnc_inst                             : Fun[
                                                    "offset"  ∷  ty.bvec (10)
                                                  ](ty.unit)
      | jn_inst                              : Fun[
                                                    "offset"  ∷  ty.bvec (10)
                                                  ](ty.unit)
      | jge_inst                             : Fun[
                                                    "offset"  ∷  ty.bvec (10)
                                                  ](ty.unit)
      | jl_inst                              : Fun[
                                                    "offset"  ∷  ty.bvec (10)
                                                  ](ty.unit)
      | jmp_inst                             : Fun[
                                                    "offset"  ∷  ty.bvec (10)
                                                  ](ty.unit)
      | encdec_jump_forwards                 : Fun[
                                                    "arg#"  ∷  ty.enum Ejump
                                                  ](ty.bvec (3))
      | encdec_jump_backwards                : Fun[
                                                    "arg#"  ∷  ty.bvec (3)
                                                  ](ty.enum Ejump)
      | encdec_jump_forwards_matches         : Fun[
                                                    "arg#"  ∷  ty.enum Ejump
                                                  ](ty.bool)
      | encdec_jump_backwards_matches        : Fun[
                                                    "arg#"  ∷  ty.bvec (3)
                                                  ](ty.bool)
      | formatAst                            : Fun[
                                                    "merge#var"  ∷  ty.union Uast
                                                  ](ty.string)
      | encdec_forwards                      : Fun[
                                                    "arg#"  ∷  ty.union Uast
                                                  ](ty.bvec (16))
      | encdec_forwards_matches              : Fun[
                                                    "arg#"  ∷  ty.union Uast
                                                  ](ty.bool)
      | execute_SINGLEOP                     : Fun[
                                                    "op"  ∷  ty.enum Esingleop;
                                                    "BW"  ∷  ty.enum Ebw;
                                                    "addressingMode"  ∷  ty.enum Eam;
                                                    "reg"  ∷  ty.enum Eregister
                                                  ](ty.unit)
      | execute_JUMP                         : Fun[
                                                    "op"  ∷  ty.enum Ejump;
                                                    "offset"  ∷  ty.bvec (10)
                                                  ](ty.unit)
      | execute_DOUBLEOP                     : Fun[
                                                    "op"  ∷  ty.enum Edoubleop;
                                                    "BW"  ∷  ty.enum Ebw;
                                                    "sourceRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeSource"  ∷  ty.enum Eam;
                                                    "destinationRegister"  ∷  ty.enum Eregister;
                                                    "addressingModeDestination"  ∷  ty.enum Eam
                                                  ](ty.unit)
      | execute_DOESNOTUNDERSTAND            : Fun[
                                                    "a"  ∷  ty.bvec (16)
                                                  ](ty.unit)
      | execute                              : Fun[
                                                    "merge#var"  ∷  ty.union Uast
                                                  ](ty.unit)
      | initialize_registers                 : Fun[
                                                    "_ж4254"  ∷  ty.unit
                                                  ](ty.unit).
    Definition 𝑭  : PCtx -> Ty -> Set := Fun.
    Definition 𝑭𝑿 : PCtx -> Ty -> Set := fun _ _ => Empty_set.
    Definition 𝑳  : PCtx -> Set := fun _ => Empty_set.
  End FunDeclKit.
  
  Include FunDeclMixin UntitledBase.
  
  Section FunDefKit.
    (*
      Extended type
        parameter v
          ?[0:4]
        return value
          ?[1]
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
      
      [1] : Sail type: bitvector(4)
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_neg_vec4 : Stm [
                                    "v"  ∷  ty.bvec (4)
                                  ]
                                  (ty.bvec (4)) :=
      stm_exp (exp_binop bop.bvsub (exp_val (ty.bvec 4) ([bv 0])) (exp_var "v")).
    
    (*
      Extended type
        parameter arg#
          BW
        return value
          ?[2]
      
      [0] : Sail type: bitvector(1)
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_bitmaping_forwards : Stm [
                                              "arg#"  ∷  ty.enum Ebw
                                            ]
                                            (ty.bvec (1)) :=
      stm_let "ж0"
              (ty.enum Ebw)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Ebw
                              (stm_exp (exp_var "ж0"))
                              (fun K => match K with
                                        | BYTE_INSTRUCTION => stm_exp (exp_val (ty.bvec 1) ([bv 1]))
                                        | WORD_INSTRUCTION => stm_exp (exp_val (ty.bvec 1) ([bv 0]))
                                        end)).
    
    (*
      Extended type
        parameter arg#
          ?[3:1]
        return value
          BW
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_bitmaping_backwards : Stm [
                                               "arg#"  ∷  ty.bvec (1)
                                             ]
                                             (ty.enum Ebw) :=
      stm_let "b__0"
              (ty.bvec (1))
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#0"
                       (ty.bool)
                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 1) ([bv 0])))))
                       (stm_let "ж4"
                                (ty.bool)
                                (stm_exp (exp_var "ga#0"))
                                (stm_if ((stm_exp (exp_var "ж4")))
                                        (stm_exp (exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))
                                        (stm_exp (exp_val (ty.enum Ebw) (BYTE_INSTRUCTION)))))).
    
    (*
      Extended type
        parameter arg#
          BW
        return value
          $0
    *)
    Definition fun_bitmaping_forwards_matches : Stm [
                                                      "arg#"  ∷  ty.enum Ebw
                                                    ]
                                                    (ty.bool) :=
      stm_let "ж5"
              (ty.enum Ebw)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Ebw
                              (stm_exp (exp_var "ж5"))
                              (fun K => match K with
                                        | BYTE_INSTRUCTION => stm_exp (exp_true)
                                        | WORD_INSTRUCTION => stm_exp (exp_true)
                                        end)).
    
    (*
      Extended type
        parameter arg#
          ?[4:1]
        return value
          $0
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_bitmaping_backwards_matches : Stm [
                                                       "arg#"  ∷  ty.bvec (1)
                                                     ]
                                                     (ty.bool) :=
      stm_let "b__0"
              (ty.bvec (1))
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#1"
                       (ty.bool)
                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 1) ([bv 0])))))
                       (stm_let "ж10"
                                (ty.bool)
                                (stm_exp (exp_var "ga#1"))
                                (stm_if ((stm_exp (exp_var "ж10")))
                                        (stm_exp (exp_true))
                                        (stm_let "ga#2"
                                                 (ty.bool)
                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 1) ([bv 1])))))
                                                 (stm_let "ж9"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#2"))
                                                          (stm_if ((stm_exp (exp_var "ж9")))
                                                                  (stm_exp (exp_true))
                                                                  (stm_exp (exp_false)))))))).
    
    (*
      Extended type
        parameter reg
          Register
        return value
          string
    *)
    Definition fun_regName : Stm [
                                   "reg"  ∷  ty.enum Eregister
                                 ]
                                 (ty.string) :=
      stm_let "ж11"
              (ty.enum Eregister)
              (stm_exp (exp_var "reg"))
              (stm_match_enum Eregister
                              (stm_exp (exp_var "ж11"))
                              (fun K => match K with
                                        | CG2   => stm_exp (exp_string "CG2_reg")
                                        | PC    => stm_exp (exp_string "PC_reg")
                                        | R10   => stm_exp (exp_string "R10_reg")
                                        | R11   => stm_exp (exp_string "R11_reg")
                                        | R12   => stm_exp (exp_string "R12_reg")
                                        | R13   => stm_exp (exp_string "R13_reg")
                                        | R14   => stm_exp (exp_string "R14_reg")
                                        | R15   => stm_exp (exp_string "R15_reg")
                                        | R4    => stm_exp (exp_string "R4_reg")
                                        | R5    => stm_exp (exp_string "R5_reg")
                                        | R6    => stm_exp (exp_string "R6_reg")
                                        | R7    => stm_exp (exp_string "R7_reg")
                                        | R8    => stm_exp (exp_string "R8_reg")
                                        | R9    => stm_exp (exp_string "R9_reg")
                                        | SP    => stm_exp (exp_string "SP_reg")
                                        | SRCG1 => stm_exp (exp_string "SRCG1_reg")
                                        end)).
    
    (*
      Extended type
        parameter am
          AM
        return value
          string
    *)
    Definition fun_AMstring : Stm [
                                    "am"  ∷  ty.enum Eam
                                  ]
                                  (ty.string) :=
      stm_let "ж29"
              (ty.enum Eam)
              (stm_exp (exp_var "am"))
              (stm_match_enum Eam
                              (stm_exp (exp_var "ж29"))
                              (fun K => match K with
                                        | INDEXED_MODE                => stm_exp (exp_string "Indexed mode")
                                        | INDIRECT_AUTOINCREMENT_MODE => stm_exp (exp_string "Indirect Autoincrement Mode")
                                        | INDIRECT_REGISTER_MODE      => stm_exp (exp_string "Indirect register mode")
                                        | REGISTER_MODE               => stm_exp (exp_string "Register mode")
                                        end)).
    
    (*
      Extended type
        parameter bw
          BW
        return value
          string
    *)
    Definition fun_BWstring : Stm [
                                    "bw"  ∷  ty.enum Ebw
                                  ]
                                  (ty.string) :=
      stm_let "ж35"
              (ty.enum Ebw)
              (stm_exp (exp_var "bw"))
              (stm_match_enum Ebw
                              (stm_exp (exp_var "ж35"))
                              (fun K => match K with
                                        | BYTE_INSTRUCTION => stm_exp (exp_string ".b")
                                        | WORD_INSTRUCTION => stm_exp (exp_string ".w")
                                        end)).
    
    (*
      Extended type
        parameter bw
          BW
        return value
          string
    *)
    Definition fun_BWSizeString : Stm [
                                        "bw"  ∷  ty.enum Ebw
                                      ]
                                      (ty.string) :=
      stm_let "ж39"
              (ty.enum Ebw)
              (stm_exp (exp_var "bw"))
              (stm_match_enum Ebw
                              (stm_exp (exp_var "ж39"))
                              (fun K => match K with
                                        | BYTE_INSTRUCTION => stm_exp (exp_string ".8")
                                        | WORD_INSTRUCTION => stm_exp (exp_string ".16")
                                        end)).
    
    (*
      Extended type
        parameter op
          doubleop
        return value
          string
    *)
    Definition fun_duopName : Stm [
                                    "op"  ∷  ty.enum Edoubleop
                                  ]
                                  (ty.string) :=
      stm_let "ж43"
              (ty.enum Edoubleop)
              (stm_exp (exp_var "op"))
              (stm_match_enum Edoubleop
                              (stm_exp (exp_var "ж43"))
                              (fun K => match K with
                                        | ADD  => stm_exp (exp_string "ADD")
                                        | ADDC => stm_exp (exp_string "ADDC")
                                        | AND  => stm_exp (exp_string "AND")
                                        | BIC  => stm_exp (exp_string "BIC")
                                        | BIS  => stm_exp (exp_string "BIS")
                                        | BIT  => stm_exp (exp_string "BIT")
                                        | CMP  => stm_exp (exp_string "CMP")
                                        | DADD => stm_exp (exp_string "DADD")
                                        | MOV  => stm_exp (exp_string "MOV")
                                        | SUB  => stm_exp (exp_string "SUB")
                                        | SUBC => stm_exp (exp_string "SUBC")
                                        | XOR  => stm_exp (exp_string "XOR")
                                        end)).
    
    (*
      Extended type
        parameter op
          singleop
        return value
          string
    *)
    Definition fun_singleopName : Stm [
                                        "op"  ∷  ty.enum Esingleop
                                      ]
                                      (ty.string) :=
      stm_let "ж57"
              (ty.enum Esingleop)
              (stm_exp (exp_var "op"))
              (stm_match_enum Esingleop
                              (stm_exp (exp_var "ж57"))
                              (fun K => match K with
                                        | CALL => stm_exp (exp_string "CALL")
                                        | PUSH => stm_exp (exp_string "PUSH")
                                        | RETI => stm_exp (exp_string "RETI")
                                        | RRA  => stm_exp (exp_string "RRA")
                                        | RRC  => stm_exp (exp_string "RRC")
                                        | SWPB => stm_exp (exp_string "SWPB")
                                        | SXT  => stm_exp (exp_string "SXT")
                                        end)).
    
    (*
      Extended type
        parameter op
          jump
        return value
          string
    *)
    Definition fun_jumpName : Stm [
                                    "op"  ∷  ty.enum Ejump
                                  ]
                                  (ty.string) :=
      stm_let "ж66"
              (ty.enum Ejump)
              (stm_exp (exp_var "op"))
              (stm_match_enum Ejump
                              (stm_exp (exp_var "ж66"))
                              (fun K => match K with
                                        | JC  => stm_exp (exp_string "JC")
                                        | JEQ => stm_exp (exp_string "JEQ")
                                        | JGE => stm_exp (exp_string "JGE")
                                        | JL  => stm_exp (exp_string "JL")
                                        | JMP => stm_exp (exp_string "JMP")
                                        | JN  => stm_exp (exp_string "JN")
                                        | JNC => stm_exp (exp_string "JNC")
                                        | JNE => stm_exp (exp_string "JNE")
                                        end)).
    
    (*
      Extended type
        parameter n
          int($0)
        parameter s
          string
        return value
          unit
      
      [0] : Not yet implemented; see nanosail/NanosailToMicrosail/FunctionCalls.ml line 575 (%s's indices should be known at compile time)
      
      [1] : Not yet implemented; see nanosail/NanosailToMicrosail/FunctionCalls.ml line 576 (%s's indices should be known at compile time)
    *)
    Definition fun_logWithVerbosity : Stm [
                                            "n"  ∷  ty.int;
                                            "s"  ∷  ty.string
                                          ]
                                          (ty.unit) :=
      stm_val ty.unit tt.

    (*
      Extended type
        parameter arg#
          Register
        return value
          ?[7]
      
      [0] : Sail type: bitvector(4)
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_RegisterMapping_forwards : Stm [
                                                    "arg#"  ∷  ty.enum Eregister
                                                  ]
                                                  (ty.bvec (4)) :=
      stm_let "ж78"
              (ty.enum Eregister)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Eregister
                              (stm_exp (exp_var "ж78"))
                              (fun K => match K with
                                        | CG2   => stm_exp (exp_val (ty.bvec 4) ([bv 3]))
                                        | PC    => stm_exp (exp_val (ty.bvec 4) ([bv 0]))
                                        | R10   => stm_exp (exp_val (ty.bvec 4) ([bv 10]))
                                        | R11   => stm_exp (exp_val (ty.bvec 4) ([bv 11]))
                                        | R12   => stm_exp (exp_val (ty.bvec 4) ([bv 12]))
                                        | R13   => stm_exp (exp_val (ty.bvec 4) ([bv 13]))
                                        | R14   => stm_exp (exp_val (ty.bvec 4) ([bv 14]))
                                        | R15   => stm_exp (exp_val (ty.bvec 4) ([bv 15]))
                                        | R4    => stm_exp (exp_val (ty.bvec 4) ([bv 4]))
                                        | R5    => stm_exp (exp_val (ty.bvec 4) ([bv 5]))
                                        | R6    => stm_exp (exp_val (ty.bvec 4) ([bv 6]))
                                        | R7    => stm_exp (exp_val (ty.bvec 4) ([bv 7]))
                                        | R8    => stm_exp (exp_val (ty.bvec 4) ([bv 8]))
                                        | R9    => stm_exp (exp_val (ty.bvec 4) ([bv 9]))
                                        | SP    => stm_exp (exp_val (ty.bvec 4) ([bv 1]))
                                        | SRCG1 => stm_exp (exp_val (ty.bvec 4) ([bv 2]))
                                        end)).
    
    (*
      Extended type
        parameter arg#
          ?[8:4]
        return value
          Register
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_RegisterMapping_backwards : Stm [
                                                     "arg#"  ∷  ty.bvec (4)
                                                   ]
                                                   (ty.enum Eregister) :=
      stm_let "b__0"
              (ty.bvec (4))
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#5"
                       (ty.bool)
                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 0])))))
                       (stm_let "ж110"
                                (ty.bool)
                                (stm_exp (exp_var "ga#5"))
                                (stm_if ((stm_exp (exp_var "ж110")))
                                        (stm_exp (exp_val (ty.enum Eregister) (PC)))
                                        (stm_let "ga#6"
                                                 (ty.bool)
                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 1])))))
                                                 (stm_let "ж109"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#6"))
                                                          (stm_if ((stm_exp (exp_var "ж109")))
                                                                  (stm_exp (exp_val (ty.enum Eregister) (SP)))
                                                                  (stm_let "ga#7"
                                                                           (ty.bool)
                                                                           (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 2])))))
                                                                           (stm_let "ж108"
                                                                                    (ty.bool)
                                                                                    (stm_exp (exp_var "ga#7"))
                                                                                    (stm_if ((stm_exp (exp_var "ж108")))
                                                                                            (stm_exp (exp_val (ty.enum Eregister) (SRCG1)))
                                                                                            (stm_let "ga#8"
                                                                                                     (ty.bool)
                                                                                                     (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 3])))))
                                                                                                     (stm_let "ж107"
                                                                                                              (ty.bool)
                                                                                                              (stm_exp (exp_var "ga#8"))
                                                                                                              (stm_if ((stm_exp (exp_var "ж107")))
                                                                                                                      (stm_exp (exp_val (ty.enum Eregister) (CG2)))
                                                                                                                      (stm_let "ga#9"
                                                                                                                               (ty.bool)
                                                                                                                               (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 4])))))
                                                                                                                               (stm_let "ж106"
                                                                                                                                        (ty.bool)
                                                                                                                                        (stm_exp (exp_var "ga#9"))
                                                                                                                                        (stm_if ((stm_exp (exp_var "ж106")))
                                                                                                                                                (stm_exp (exp_val (ty.enum Eregister) (R4)))
                                                                                                                                                (stm_let "ga#10"
                                                                                                                                                         (ty.bool)
                                                                                                                                                         (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 5])))))
                                                                                                                                                         (stm_let "ж105"
                                                                                                                                                                  (ty.bool)
                                                                                                                                                                  (stm_exp (exp_var "ga#10"))
                                                                                                                                                                  (stm_if ((stm_exp (exp_var "ж105")))
                                                                                                                                                                          (stm_exp (exp_val (ty.enum Eregister) (R5)))
                                                                                                                                                                          (stm_let "ga#11"
                                                                                                                                                                                   (ty.bool)
                                                                                                                                                                                   (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 6])))))
                                                                                                                                                                                   (stm_let "ж104"
                                                                                                                                                                                            (ty.bool)
                                                                                                                                                                                            (stm_exp (exp_var "ga#11"))
                                                                                                                                                                                            (stm_if ((stm_exp (exp_var "ж104")))
                                                                                                                                                                                                    (stm_exp (exp_val (ty.enum Eregister) (R6)))
                                                                                                                                                                                                    (stm_let "ga#12"
                                                                                                                                                                                                             (ty.bool)
                                                                                                                                                                                                             (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 7])))))
                                                                                                                                                                                                             (stm_let "ж103"
                                                                                                                                                                                                                      (ty.bool)
                                                                                                                                                                                                                      (stm_exp (exp_var "ga#12"))
                                                                                                                                                                                                                      (stm_if ((stm_exp (exp_var "ж103")))
                                                                                                                                                                                                                              (stm_exp (exp_val (ty.enum Eregister) (R7)))
                                                                                                                                                                                                                              (stm_let "ga#13"
                                                                                                                                                                                                                                       (ty.bool)
                                                                                                                                                                                                                                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 8])))))
                                                                                                                                                                                                                                       (stm_let "ж102"
                                                                                                                                                                                                                                                (ty.bool)
                                                                                                                                                                                                                                                (stm_exp (exp_var "ga#13"))
                                                                                                                                                                                                                                                (stm_if ((stm_exp (exp_var "ж102")))
                                                                                                                                                                                                                                                        (stm_exp (exp_val (ty.enum Eregister) (R8)))
                                                                                                                                                                                                                                                        (stm_let "ga#14"
                                                                                                                                                                                                                                                                 (ty.bool)
                                                                                                                                                                                                                                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 9])))))
                                                                                                                                                                                                                                                                 (stm_let "ж101"
                                                                                                                                                                                                                                                                          (ty.bool)
                                                                                                                                                                                                                                                                          (stm_exp (exp_var "ga#14"))
                                                                                                                                                                                                                                                                          (stm_if ((stm_exp (exp_var "ж101")))
                                                                                                                                                                                                                                                                                  (stm_exp (exp_val (ty.enum Eregister) (R9)))
                                                                                                                                                                                                                                                                                  (stm_let "ga#15"
                                                                                                                                                                                                                                                                                           (ty.bool)
                                                                                                                                                                                                                                                                                           (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 10])))))
                                                                                                                                                                                                                                                                                           (stm_let "ж100"
                                                                                                                                                                                                                                                                                                    (ty.bool)
                                                                                                                                                                                                                                                                                                    (stm_exp (exp_var "ga#15"))
                                                                                                                                                                                                                                                                                                    (stm_if ((stm_exp (exp_var "ж100")))
                                                                                                                                                                                                                                                                                                            (stm_exp (exp_val (ty.enum Eregister) (R10)))
                                                                                                                                                                                                                                                                                                            (stm_let "ga#16"
                                                                                                                                                                                                                                                                                                                     (ty.bool)
                                                                                                                                                                                                                                                                                                                     (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 11])))))
                                                                                                                                                                                                                                                                                                                     (stm_let "ж99"
                                                                                                                                                                                                                                                                                                                              (ty.bool)
                                                                                                                                                                                                                                                                                                                              (stm_exp (exp_var "ga#16"))
                                                                                                                                                                                                                                                                                                                              (stm_if ((stm_exp (exp_var "ж99")))
                                                                                                                                                                                                                                                                                                                                      (stm_exp (exp_val (ty.enum Eregister) (R11)))
                                                                                                                                                                                                                                                                                                                                      (stm_let "ga#17"
                                                                                                                                                                                                                                                                                                                                               (ty.bool)
                                                                                                                                                                                                                                                                                                                                               (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 12])))))
                                                                                                                                                                                                                                                                                                                                               (stm_let "ж98"
                                                                                                                                                                                                                                                                                                                                                        (ty.bool)
                                                                                                                                                                                                                                                                                                                                                        (stm_exp (exp_var "ga#17"))
                                                                                                                                                                                                                                                                                                                                                        (stm_if ((stm_exp (exp_var "ж98")))
                                                                                                                                                                                                                                                                                                                                                                (stm_exp (exp_val (ty.enum Eregister) (R12)))
                                                                                                                                                                                                                                                                                                                                                                (stm_let "ga#18"
                                                                                                                                                                                                                                                                                                                                                                         (ty.bool)
                                                                                                                                                                                                                                                                                                                                                                         (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 13])))))
                                                                                                                                                                                                                                                                                                                                                                         (stm_let "ж97"
                                                                                                                                                                                                                                                                                                                                                                                  (ty.bool)
                                                                                                                                                                                                                                                                                                                                                                                  (stm_exp (exp_var "ga#18"))
                                                                                                                                                                                                                                                                                                                                                                                  (stm_if ((stm_exp (exp_var "ж97")))
                                                                                                                                                                                                                                                                                                                                                                                          (stm_exp (exp_val (ty.enum Eregister) (R13)))
                                                                                                                                                                                                                                                                                                                                                                                          (stm_let "ga#19"
                                                                                                                                                                                                                                                                                                                                                                                                   (ty.bool)
                                                                                                                                                                                                                                                                                                                                                                                                   (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 14])))))
                                                                                                                                                                                                                                                                                                                                                                                                   (stm_let "ж96"
                                                                                                                                                                                                                                                                                                                                                                                                            (ty.bool)
                                                                                                                                                                                                                                                                                                                                                                                                            (stm_exp (exp_var "ga#19"))
                                                                                                                                                                                                                                                                                                                                                                                                            (stm_if ((stm_exp (exp_var "ж96")))
                                                                                                                                                                                                                                                                                                                                                                                                                    (stm_exp (exp_val (ty.enum Eregister) (R14)))
                                                                                                                                                                                                                                                                                                                                                                                                                    (stm_exp (exp_val (ty.enum Eregister) (R15)))))))))))))))))))))))))))))))))))))))))))))))).
    
    (*
      Extended type
        parameter arg#
          Register
        return value
          $0
    *)
    Definition fun_RegisterMapping_forwards_matches : Stm [
                                                            "arg#"  ∷  ty.enum Eregister
                                                          ]
                                                          (ty.bool) :=
      stm_let "ж111"
              (ty.enum Eregister)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Eregister
                              (stm_exp (exp_var "ж111"))
                              (fun K => match K with
                                        | CG2   => stm_exp (exp_true)
                                        | PC    => stm_exp (exp_true)
                                        | R10   => stm_exp (exp_true)
                                        | R11   => stm_exp (exp_true)
                                        | R12   => stm_exp (exp_true)
                                        | R13   => stm_exp (exp_true)
                                        | R14   => stm_exp (exp_true)
                                        | R15   => stm_exp (exp_true)
                                        | R4    => stm_exp (exp_true)
                                        | R5    => stm_exp (exp_true)
                                        | R6    => stm_exp (exp_true)
                                        | R7    => stm_exp (exp_true)
                                        | R8    => stm_exp (exp_true)
                                        | R9    => stm_exp (exp_true)
                                        | SP    => stm_exp (exp_true)
                                        | SRCG1 => stm_exp (exp_true)
                                        end)).
    
    (*
      Extended type
        parameter arg#
          ?[9:4]
        return value
          $0
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_RegisterMapping_backwards_matches : Stm [
                                                             "arg#"  ∷  ty.bvec (4)
                                                           ]
                                                           (ty.bool) :=
      stm_let "b__0"
              (ty.bvec (4))
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#20"
                       (ty.bool)
                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 0])))))
                       (stm_let "ж144"
                                (ty.bool)
                                (stm_exp (exp_var "ga#20"))
                                (stm_if ((stm_exp (exp_var "ж144")))
                                        (stm_exp (exp_true))
                                        (stm_let "ga#21"
                                                 (ty.bool)
                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 1])))))
                                                 (stm_let "ж143"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#21"))
                                                          (stm_if ((stm_exp (exp_var "ж143")))
                                                                  (stm_exp (exp_true))
                                                                  (stm_let "ga#22"
                                                                           (ty.bool)
                                                                           (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 2])))))
                                                                           (stm_let "ж142"
                                                                                    (ty.bool)
                                                                                    (stm_exp (exp_var "ga#22"))
                                                                                    (stm_if ((stm_exp (exp_var "ж142")))
                                                                                            (stm_exp (exp_true))
                                                                                            (stm_let "ga#23"
                                                                                                     (ty.bool)
                                                                                                     (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 3])))))
                                                                                                     (stm_let "ж141"
                                                                                                              (ty.bool)
                                                                                                              (stm_exp (exp_var "ga#23"))
                                                                                                              (stm_if ((stm_exp (exp_var "ж141")))
                                                                                                                      (stm_exp (exp_true))
                                                                                                                      (stm_let "ga#24"
                                                                                                                               (ty.bool)
                                                                                                                               (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 4])))))
                                                                                                                               (stm_let "ж140"
                                                                                                                                        (ty.bool)
                                                                                                                                        (stm_exp (exp_var "ga#24"))
                                                                                                                                        (stm_if ((stm_exp (exp_var "ж140")))
                                                                                                                                                (stm_exp (exp_true))
                                                                                                                                                (stm_let "ga#25"
                                                                                                                                                         (ty.bool)
                                                                                                                                                         (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 5])))))
                                                                                                                                                         (stm_let "ж139"
                                                                                                                                                                  (ty.bool)
                                                                                                                                                                  (stm_exp (exp_var "ga#25"))
                                                                                                                                                                  (stm_if ((stm_exp (exp_var "ж139")))
                                                                                                                                                                          (stm_exp (exp_true))
                                                                                                                                                                          (stm_let "ga#26"
                                                                                                                                                                                   (ty.bool)
                                                                                                                                                                                   (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 6])))))
                                                                                                                                                                                   (stm_let "ж138"
                                                                                                                                                                                            (ty.bool)
                                                                                                                                                                                            (stm_exp (exp_var "ga#26"))
                                                                                                                                                                                            (stm_if ((stm_exp (exp_var "ж138")))
                                                                                                                                                                                                    (stm_exp (exp_true))
                                                                                                                                                                                                    (stm_let "ga#27"
                                                                                                                                                                                                             (ty.bool)
                                                                                                                                                                                                             (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 7])))))
                                                                                                                                                                                                             (stm_let "ж137"
                                                                                                                                                                                                                      (ty.bool)
                                                                                                                                                                                                                      (stm_exp (exp_var "ga#27"))
                                                                                                                                                                                                                      (stm_if ((stm_exp (exp_var "ж137")))
                                                                                                                                                                                                                              (stm_exp (exp_true))
                                                                                                                                                                                                                              (stm_let "ga#28"
                                                                                                                                                                                                                                       (ty.bool)
                                                                                                                                                                                                                                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 8])))))
                                                                                                                                                                                                                                       (stm_let "ж136"
                                                                                                                                                                                                                                                (ty.bool)
                                                                                                                                                                                                                                                (stm_exp (exp_var "ga#28"))
                                                                                                                                                                                                                                                (stm_if ((stm_exp (exp_var "ж136")))
                                                                                                                                                                                                                                                        (stm_exp (exp_true))
                                                                                                                                                                                                                                                        (stm_let "ga#29"
                                                                                                                                                                                                                                                                 (ty.bool)
                                                                                                                                                                                                                                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 9])))))
                                                                                                                                                                                                                                                                 (stm_let "ж135"
                                                                                                                                                                                                                                                                          (ty.bool)
                                                                                                                                                                                                                                                                          (stm_exp (exp_var "ga#29"))
                                                                                                                                                                                                                                                                          (stm_if ((stm_exp (exp_var "ж135")))
                                                                                                                                                                                                                                                                                  (stm_exp (exp_true))
                                                                                                                                                                                                                                                                                  (stm_let "ga#30"
                                                                                                                                                                                                                                                                                           (ty.bool)
                                                                                                                                                                                                                                                                                           (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 10])))))
                                                                                                                                                                                                                                                                                           (stm_let "ж134"
                                                                                                                                                                                                                                                                                                    (ty.bool)
                                                                                                                                                                                                                                                                                                    (stm_exp (exp_var "ga#30"))
                                                                                                                                                                                                                                                                                                    (stm_if ((stm_exp (exp_var "ж134")))
                                                                                                                                                                                                                                                                                                            (stm_exp (exp_true))
                                                                                                                                                                                                                                                                                                            (stm_let "ga#31"
                                                                                                                                                                                                                                                                                                                     (ty.bool)
                                                                                                                                                                                                                                                                                                                     (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 11])))))
                                                                                                                                                                                                                                                                                                                     (stm_let "ж133"
                                                                                                                                                                                                                                                                                                                              (ty.bool)
                                                                                                                                                                                                                                                                                                                              (stm_exp (exp_var "ga#31"))
                                                                                                                                                                                                                                                                                                                              (stm_if ((stm_exp (exp_var "ж133")))
                                                                                                                                                                                                                                                                                                                                      (stm_exp (exp_true))
                                                                                                                                                                                                                                                                                                                                      (stm_let "ga#32"
                                                                                                                                                                                                                                                                                                                                               (ty.bool)
                                                                                                                                                                                                                                                                                                                                               (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 12])))))
                                                                                                                                                                                                                                                                                                                                               (stm_let "ж132"
                                                                                                                                                                                                                                                                                                                                                        (ty.bool)
                                                                                                                                                                                                                                                                                                                                                        (stm_exp (exp_var "ga#32"))
                                                                                                                                                                                                                                                                                                                                                        (stm_if ((stm_exp (exp_var "ж132")))
                                                                                                                                                                                                                                                                                                                                                                (stm_exp (exp_true))
                                                                                                                                                                                                                                                                                                                                                                (stm_let "ga#33"
                                                                                                                                                                                                                                                                                                                                                                         (ty.bool)
                                                                                                                                                                                                                                                                                                                                                                         (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 13])))))
                                                                                                                                                                                                                                                                                                                                                                         (stm_let "ж131"
                                                                                                                                                                                                                                                                                                                                                                                  (ty.bool)
                                                                                                                                                                                                                                                                                                                                                                                  (stm_exp (exp_var "ga#33"))
                                                                                                                                                                                                                                                                                                                                                                                  (stm_if ((stm_exp (exp_var "ж131")))
                                                                                                                                                                                                                                                                                                                                                                                          (stm_exp (exp_true))
                                                                                                                                                                                                                                                                                                                                                                                          (stm_let "ga#34"
                                                                                                                                                                                                                                                                                                                                                                                                   (ty.bool)
                                                                                                                                                                                                                                                                                                                                                                                                   (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 14])))))
                                                                                                                                                                                                                                                                                                                                                                                                   (stm_let "ж130"
                                                                                                                                                                                                                                                                                                                                                                                                            (ty.bool)
                                                                                                                                                                                                                                                                                                                                                                                                            (stm_exp (exp_var "ga#34"))
                                                                                                                                                                                                                                                                                                                                                                                                            (stm_if ((stm_exp (exp_var "ж130")))
                                                                                                                                                                                                                                                                                                                                                                                                                    (stm_exp (exp_true))
                                                                                                                                                                                                                                                                                                                                                                                                                    (stm_let "ga#35"
                                                                                                                                                                                                                                                                                                                                                                                                                             (ty.bool)
                                                                                                                                                                                                                                                                                                                                                                                                                             (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 15])))))
                                                                                                                                                                                                                                                                                                                                                                                                                             (stm_let "ж129"
                                                                                                                                                                                                                                                                                                                                                                                                                                      (ty.bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                      (stm_exp (exp_var "ga#35"))
                                                                                                                                                                                                                                                                                                                                                                                                                                      (stm_if ((stm_exp (exp_var "ж129")))
                                                                                                                                                                                                                                                                                                                                                                                                                                              (stm_exp (exp_true))
                                                                                                                                                                                                                                                                                                                                                                                                                                              (stm_exp (exp_false)))))))))))))))))))))))))))))))))))))))))))))))))).
    
    (*
      Extended type
        parameter _ж145
          unit
        return value
          unit
    *)
    Definition fun_init_base_regs : Stm [
                                          "_ж145"  ∷  ty.unit
                                        ]
                                        (ty.unit) :=
      stm_seq (stm_seq (stm_let "ж146"
                                (ty.wordBits)
                                (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                (stm_write_register PC_reg (exp_var "ж146")))
                       (stm_exp (exp_val (ty.unit) (tt))))
              (stm_seq (stm_seq (stm_let "ж148"
                                         (ty.wordBits)
                                         (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                         (stm_write_register SP_reg (exp_var "ж148")))
                                (stm_exp (exp_val (ty.unit) (tt))))
                       (stm_seq (stm_seq (stm_let "ж150"
                                                  (ty.wordBits)
                                                  (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                                  (stm_write_register SRCG1_reg (exp_var "ж150")))
                                         (stm_exp (exp_val (ty.unit) (tt))))
                                (stm_seq (stm_seq (stm_let "ж152"
                                                           (ty.wordBits)
                                                           (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                                           (stm_write_register CG2_reg (exp_var "ж152")))
                                                  (stm_exp (exp_val (ty.unit) (tt))))
                                         (stm_seq (stm_seq (stm_let "ж154"
                                                                    (ty.wordBits)
                                                                    (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                                                    (stm_write_register R4_reg (exp_var "ж154")))
                                                           (stm_exp (exp_val (ty.unit) (tt))))
                                                  (stm_seq (stm_seq (stm_let "ж156"
                                                                             (ty.wordBits)
                                                                             (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                                                             (stm_write_register R5_reg (exp_var "ж156")))
                                                                    (stm_exp (exp_val (ty.unit) (tt))))
                                                           (stm_seq (stm_seq (stm_let "ж158"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                                                                      (stm_write_register R6_reg (exp_var "ж158")))
                                                                             (stm_exp (exp_val (ty.unit) (tt))))
                                                                    (stm_seq (stm_seq (stm_let "ж160"
                                                                                               (ty.wordBits)
                                                                                               (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                                                                               (stm_write_register R7_reg (exp_var "ж160")))
                                                                                      (stm_exp (exp_val (ty.unit) (tt))))
                                                                             (stm_seq (stm_seq (stm_let "ж162"
                                                                                                        (ty.wordBits)
                                                                                                        (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                                                                                        (stm_write_register R8_reg (exp_var "ж162")))
                                                                                               (stm_exp (exp_val (ty.unit) (tt))))
                                                                                      (stm_seq (stm_seq (stm_let "ж164"
                                                                                                                 (ty.wordBits)
                                                                                                                 (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                                                                                                 (stm_write_register R9_reg (exp_var "ж164")))
                                                                                                        (stm_exp (exp_val (ty.unit) (tt))))
                                                                                               (stm_seq (stm_seq (stm_let "ж166"
                                                                                                                          (ty.wordBits)
                                                                                                                          (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                                                                                                          (stm_write_register R10_reg (exp_var "ж166")))
                                                                                                                 (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                        (stm_seq (stm_seq (stm_let "ж168"
                                                                                                                                   (ty.wordBits)
                                                                                                                                   (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                                                                                                                   (stm_write_register R11_reg (exp_var "ж168")))
                                                                                                                          (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                 (stm_seq (stm_seq (stm_let "ж170"
                                                                                                                                            (ty.wordBits)
                                                                                                                                            (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                                                                                                                            (stm_write_register R12_reg (exp_var "ж170")))
                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                          (stm_seq (stm_seq (stm_let "ж172"
                                                                                                                                                     (ty.wordBits)
                                                                                                                                                     (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                                                                                                                                     (stm_write_register R13_reg (exp_var "ж172")))
                                                                                                                                            (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                                   (stm_seq (stm_seq (stm_let "ж174"
                                                                                                                                                              (ty.wordBits)
                                                                                                                                                              (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                                                                                                                                              (stm_write_register R14_reg (exp_var "ж174")))
                                                                                                                                                     (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                                            (stm_seq (stm_let "ж176"
                                                                                                                                                              (ty.wordBits)
                                                                                                                                                              (stm_exp (exp_val (ty.bvec 16) ([bv 0])))
                                                                                                                                                              (stm_write_register R15_reg (exp_var "ж176")))
                                                                                                                                                     (stm_exp (exp_val (ty.unit) (tt)))))))))))))))))).
    
    (*
      Extended type
        parameter merge#var
          WordByte
        return value
          WordByte
    *)
    Definition fun_toByte : Stm [
                                  "merge#var"  ∷  ty.union Uwordbyte
                                ]
                                (ty.union Uwordbyte) :=
      stm_let "ж207"
              (ty.union Uwordbyte)
              (stm_exp (exp_var "merge#var"))
              (stm_match_union_alt_list Uwordbyte
                                        (stm_exp (exp_var "ж207"))
                                        [
                                          existT Kbyte (MkAlt (pat_var "b") (stm_exp (exp_union Uwordbyte Kbyte (exp_var "b"))));
                                          existT Kword (MkAlt (pat_var "w") (stm_let "ga#51"
                                                                                     (ty.bvec (8))
                                                                                     (stm_exp (exp_unop (uop.vector_subrange 0 8) (exp_var "w")))
                                                                                     (stm_exp (exp_union Uwordbyte Kbyte (exp_var "ga#51")))))
                                        ]
                                        Logic.I).
    
    (*
      Extended type
        parameter merge#var
          WordByte
        return value
          $0
    *)
    Definition fun_signedWb : Stm [
                                    "merge#var"  ∷  ty.union Uwordbyte
                                  ]
                                  (ty.int) :=
      stm_let "ж213"
              (ty.union Uwordbyte)
              (stm_exp (exp_var "merge#var"))
              (stm_match_union_alt_list Uwordbyte
                                        (stm_exp (exp_var "ж213"))
                                        [
                                          existT Kbyte (MkAlt (pat_var "b") (stm_exp (exp_unop uop.signed (exp_var "b"))));
                                          existT Kword (MkAlt (pat_var "w") (stm_exp (exp_unop uop.signed (exp_var "w"))))
                                        ]
                                        Logic.I).
    
    (*
      Extended type
        parameter merge#var
          WordByte
        return value
          $0
    *)
    Definition fun_unsignedWb : Stm [
                                      "merge#var"  ∷  ty.union Uwordbyte
                                    ]
                                    (ty.int) :=
      stm_let "ж219"
              (ty.union Uwordbyte)
              (stm_exp (exp_var "merge#var"))
              (stm_match_union_alt_list Uwordbyte
                                        (stm_exp (exp_var "ж219"))
                                        [
                                          existT Kbyte (MkAlt (pat_var "b") (stm_exp (exp_unop uop.unsigned (exp_var "b"))));
                                          existT Kword (MkAlt (pat_var "w") (stm_exp (exp_unop uop.unsigned (exp_var "w"))))
                                        ]
                                        Logic.I).
    
    (*
      Extended type
        parameter x
          WordByte
        parameter y
          WordByte
        return value
          WordByte
    *)
    Definition fun_addBw : Stm [
                                 "x"  ∷  ty.union Uwordbyte;
                                 "y"  ∷  ty.union Uwordbyte
                               ]
                               (ty.union Uwordbyte) :=
      stm_let "ж225"
              (ty.prod (ty.union Uwordbyte) (ty.union Uwordbyte))
              (stm_exp (exp_binop bop.pair (exp_var "x") (exp_var "y")))
              (stm_match_prod (stm_exp (exp_var "ж225"))
                              "ж254"
                              "ж255"
                              (stm_match_union_alt_list Uwordbyte
                                                        (stm_exp (exp_var "ж254"))
                                                        [
                                                          existT Kbyte (MkAlt (pat_var "a") (stm_match_union_alt_list Uwordbyte
                                                                                                                      (stm_exp (exp_var "ж255"))
                                                                                                                      [
                                                                                                                        existT Kbyte (MkAlt (pat_var "b") (stm_let "ga#52"
                                                                                                                                                                   (ty.bvec (8))
                                                                                                                                                                   (stm_exp (exp_binop bop.bvadd (exp_var "a") (exp_var "b")))
                                                                                                                                                                   (stm_exp (exp_union Uwordbyte Kbyte (exp_var "ga#52")))));
                                                                                                                        existT Kword (MkAlt (pat_var "b") (stm_let "ga#57"
                                                                                                                                                                   (ty.bvec (16))
                                                                                                                                                                   (stm_let "ga#56"
                                                                                                                                                                            (ty.bvec (16))
                                                                                                                                                                            (stm_exp (exp_unop (uop.zext (n := 16)) (exp_var "a")))
                                                                                                                                                                            (stm_exp (exp_binop bop.bvadd (exp_var "b") (exp_var "ga#56"))))
                                                                                                                                                                   (stm_exp (exp_union Uwordbyte Kword (exp_var "ga#57")))))
                                                                                                                      ]
                                                                                                                      Logic.I));
                                                          existT Kword (MkAlt (pat_var "a") (stm_match_union_alt_list Uwordbyte
                                                                                                                      (stm_exp (exp_var "ж255"))
                                                                                                                      [
                                                                                                                        existT Kbyte (MkAlt (pat_var "b") (stm_let "ga#55"
                                                                                                                                                                   (ty.bvec (16))
                                                                                                                                                                   (stm_let "ga#54"
                                                                                                                                                                            (ty.bvec (16))
                                                                                                                                                                            (stm_exp (exp_unop (uop.zext (n := 16)) (exp_var "b")))
                                                                                                                                                                            (stm_exp (exp_binop bop.bvadd (exp_var "a") (exp_var "ga#54"))))
                                                                                                                                                                   (stm_exp (exp_union Uwordbyte Kword (exp_var "ga#55")))));
                                                                                                                        existT Kword (MkAlt (pat_var "b") (stm_let "ga#53"
                                                                                                                                                                   (ty.bvec (16))
                                                                                                                                                                   (stm_exp (exp_binop bop.bvadd (exp_var "a") (exp_var "b")))
                                                                                                                                                                   (stm_exp (exp_union Uwordbyte Kword (exp_var "ga#53")))))
                                                                                                                      ]
                                                                                                                      Logic.I))
                                                        ]
                                                        Logic.I)).
    
    (*
      Extended type
        parameter b
          ?[10:1]
        return value
          ?[11]
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
      
      [1] : Sail type: WordByte()
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: ../msp430-ipe-sail/MSP430_types.sail:15
    *)
    Definition fun_zero_extend_bit_to_byte : Stm [
                                                   "b"  ∷  ty.bvec (1)
                                                 ]
                                                 ((ty.union Uwordbyte)) :=
      stm_let "ga#58"
              (ty.bvec (8))
              (stm_exp (exp_unop (uop.zext (n := 8)) (exp_var "b")))
              (stm_exp (exp_union Uwordbyte Kbyte (exp_var "ga#58"))).
    
    (*
      Extended type
        parameter merge#var
          WordByte
        return value
          WordByte
    *)
    Definition fun_not_wordByte : Stm [
                                        "merge#var"  ∷  ty.union Uwordbyte
                                      ]
                                      (ty.union Uwordbyte) :=
      stm_let "ж256"
              (ty.union Uwordbyte)
              (stm_exp (exp_var "merge#var"))
              (stm_match_union_alt_list Uwordbyte
                                        (stm_exp (exp_var "ж256"))
                                        [
                                          existT Kbyte (MkAlt (pat_var "v") (stm_let "ga#60"
                                                                                     (ty.bvec (8))
                                                                                     (stm_exp (exp_unop uop.bvnot (exp_var "v")))
                                                                                     (stm_exp (exp_union Uwordbyte Kbyte (exp_var "ga#60")))));
                                          existT Kword (MkAlt (pat_var "v") (stm_let "ga#59"
                                                                                     (ty.bvec (16))
                                                                                     (stm_exp (exp_unop uop.bvnot (exp_var "v")))
                                                                                     (stm_exp (exp_union Uwordbyte Kword (exp_var "ga#59")))))
                                        ]
                                        Logic.I).
    
    (*
      Extended type
        parameter x
          WordByte
        parameter y
          WordByte
        return value
          WordByte
    *)
    Definition fun_and_wordByte : Stm [
                                        "x"  ∷  ty.union Uwordbyte;
                                        "y"  ∷  ty.union Uwordbyte
                                      ]
                                      (ty.union Uwordbyte) :=
      stm_let "ж262"
              (ty.prod (ty.union Uwordbyte) (ty.union Uwordbyte))
              (stm_exp (exp_binop bop.pair (exp_var "x") (exp_var "y")))
              (stm_match_prod (stm_exp (exp_var "ж262"))
                              "ж293"
                              "ж294"
                              (stm_match_union_alt_list Uwordbyte
                                                        (stm_exp (exp_var "ж293"))
                                                        [
                                                          existT Kbyte (MkAlt (pat_var "b1") (stm_match_union_alt_list Uwordbyte
                                                                                                                       (stm_exp (exp_var "ж294"))
                                                                                                                       [
                                                                                                                         existT Kbyte (MkAlt (pat_var "b2") (stm_let "ga#62"
                                                                                                                                                                     (ty.bvec (8))
                                                                                                                                                                     (stm_exp (exp_binop bop.bvand (exp_var "b1") (exp_var "b2")))
                                                                                                                                                                     (stm_exp (exp_union Uwordbyte Kbyte (exp_var "ga#62")))));
                                                                                                                         existT Kword (MkAlt (pat_var "ж278") (stm_seq (stm_exp (exp_union Uexception Knotimplemented (exp_string "not implemented")))
                                                                                                                                                                        (stm_fail (ty.union Uwordbyte) "failure")))
                                                                                                                       ]
                                                                                                                       Logic.I));
                                                          existT Kword (MkAlt (pat_var "w1") (stm_match_union_alt_list Uwordbyte
                                                                                                                       (stm_exp (exp_var "ж294"))
                                                                                                                       [
                                                                                                                         existT Kbyte (MkAlt (pat_var "ж272") (stm_seq (stm_exp (exp_union Uexception Knotimplemented (exp_string "not implemented")))
                                                                                                                                                                        (stm_fail (ty.union Uwordbyte) "failure")));
                                                                                                                         existT Kword (MkAlt (pat_var "w2") (stm_let "ga#61"
                                                                                                                                                                     (ty.bvec (16))
                                                                                                                                                                     (stm_exp (exp_binop bop.bvand (exp_var "w1") (exp_var "w2")))
                                                                                                                                                                     (stm_exp (exp_union Uwordbyte Kword (exp_var "ga#61")))))
                                                                                                                       ]
                                                                                                                       Logic.I))
                                                        ]
                                                        Logic.I)).
    
    (*
      Extended type
        parameter x
          WordByte
        parameter y
          WordByte
        return value
          WordByte
    *)
    Definition fun_or_wordByte : Stm [
                                       "x"  ∷  ty.union Uwordbyte;
                                       "y"  ∷  ty.union Uwordbyte
                                     ]
                                     (ty.union Uwordbyte) :=
      stm_let "ж295"
              (ty.prod (ty.union Uwordbyte) (ty.union Uwordbyte))
              (stm_exp (exp_binop bop.pair (exp_var "x") (exp_var "y")))
              (stm_match_prod (stm_exp (exp_var "ж295"))
                              "ж326"
                              "ж327"
                              (stm_match_union_alt_list Uwordbyte
                                                        (stm_exp (exp_var "ж326"))
                                                        [
                                                          existT Kbyte (MkAlt (pat_var "b1") (stm_match_union_alt_list Uwordbyte
                                                                                                                       (stm_exp (exp_var "ж327"))
                                                                                                                       [
                                                                                                                         existT Kbyte (MkAlt (pat_var "b2") (stm_let "ga#65"
                                                                                                                                                                     (ty.bvec (8))
                                                                                                                                                                     (stm_exp (exp_binop bop.bvor (exp_var "b1") (exp_var "b2")))
                                                                                                                                                                     (stm_exp (exp_union Uwordbyte Kbyte (exp_var "ga#65")))));
                                                                                                                         existT Kword (MkAlt (pat_var "ж311") (stm_seq (stm_exp (exp_union Uexception Knotimplemented (exp_string "not implemented")))
                                                                                                                                                                        (stm_fail (ty.union Uwordbyte) "failure")))
                                                                                                                       ]
                                                                                                                       Logic.I));
                                                          existT Kword (MkAlt (pat_var "w1") (stm_match_union_alt_list Uwordbyte
                                                                                                                       (stm_exp (exp_var "ж327"))
                                                                                                                       [
                                                                                                                         existT Kbyte (MkAlt (pat_var "ж305") (stm_seq (stm_exp (exp_union Uexception Knotimplemented (exp_string "not implemented")))
                                                                                                                                                                        (stm_fail (ty.union Uwordbyte) "failure")));
                                                                                                                         existT Kword (MkAlt (pat_var "w2") (stm_let "ga#64"
                                                                                                                                                                     (ty.bvec (16))
                                                                                                                                                                     (stm_exp (exp_binop bop.bvor (exp_var "w1") (exp_var "w2")))
                                                                                                                                                                     (stm_exp (exp_union Uwordbyte Kword (exp_var "ga#64")))))
                                                                                                                       ]
                                                                                                                       Logic.I))
                                                        ]
                                                        Logic.I)).
    
    (*
      Extended type
        parameter x
          WordByte
        parameter y
          WordByte
        return value
          WordByte
    *)
    Definition fun_xor_wordByte : Stm [
                                        "x"  ∷  ty.union Uwordbyte;
                                        "y"  ∷  ty.union Uwordbyte
                                      ]
                                      (ty.union Uwordbyte) :=
      stm_let "ж328"
              (ty.prod (ty.union Uwordbyte) (ty.union Uwordbyte))
              (stm_exp (exp_binop bop.pair (exp_var "x") (exp_var "y")))
              (stm_match_prod (stm_exp (exp_var "ж328"))
                              "ж359"
                              "ж360"
                              (stm_match_union_alt_list Uwordbyte
                                                        (stm_exp (exp_var "ж359"))
                                                        [
                                                          existT Kbyte (MkAlt (pat_var "b1") (stm_match_union_alt_list Uwordbyte
                                                                                                                       (stm_exp (exp_var "ж360"))
                                                                                                                       [
                                                                                                                         existT Kbyte (MkAlt (pat_var "b2") (stm_let "ga#68"
                                                                                                                                                                     (ty.bvec (8))
                                                                                                                                                                     (stm_exp (exp_binop bop.bvxor (exp_var "b1") (exp_var "b2")))
                                                                                                                                                                     (stm_exp (exp_union Uwordbyte Kbyte (exp_var "ga#68")))));
                                                                                                                         existT Kword (MkAlt (pat_var "ж344") (stm_seq (stm_exp (exp_union Uexception Knotimplemented (exp_string "not implemented")))
                                                                                                                                                                        (stm_fail (ty.union Uwordbyte) "failure")))
                                                                                                                       ]
                                                                                                                       Logic.I));
                                                          existT Kword (MkAlt (pat_var "w1") (stm_match_union_alt_list Uwordbyte
                                                                                                                       (stm_exp (exp_var "ж360"))
                                                                                                                       [
                                                                                                                         existT Kbyte (MkAlt (pat_var "ж338") (stm_seq (stm_exp (exp_union Uexception Knotimplemented (exp_string "not implemented")))
                                                                                                                                                                        (stm_fail (ty.union Uwordbyte) "failure")));
                                                                                                                         existT Kword (MkAlt (pat_var "w2") (stm_let "ga#67"
                                                                                                                                                                     (ty.bvec (16))
                                                                                                                                                                     (stm_exp (exp_binop bop.bvxor (exp_var "w1") (exp_var "w2")))
                                                                                                                                                                     (stm_exp (exp_union Uwordbyte Kword (exp_var "ga#67")))))
                                                                                                                       ]
                                                                                                                       Logic.I))
                                                        ]
                                                        Logic.I)).
    
    (*
      Extended type
        parameter x
          WordByte
        parameter y
          WordByte
        return value
          $0
    *)
    Definition fun_eq_wordByte : Stm [
                                       "x"  ∷  ty.union Uwordbyte;
                                       "y"  ∷  ty.union Uwordbyte
                                     ]
                                     (ty.bool) :=
      stm_let "ж361"
              (ty.prod (ty.union Uwordbyte) (ty.union Uwordbyte))
              (stm_exp (exp_binop bop.pair (exp_var "x") (exp_var "y")))
              (stm_match_prod (stm_exp (exp_var "ж361"))
                              "ж392"
                              "ж393"
                              (stm_match_union_alt_list Uwordbyte
                                                        (stm_exp (exp_var "ж392"))
                                                        [
                                                          existT Kbyte (MkAlt (pat_var "b1") (stm_match_union_alt_list Uwordbyte
                                                                                                                       (stm_exp (exp_var "ж393"))
                                                                                                                       [
                                                                                                                         existT Kbyte (MkAlt (pat_var "b2") (stm_exp (((exp_var "b1") = (exp_var "b2")))));
                                                                                                                         existT Kword (MkAlt (pat_var "ж377") (stm_exp (exp_false)))
                                                                                                                       ]
                                                                                                                       Logic.I));
                                                          existT Kword (MkAlt (pat_var "w1") (stm_match_union_alt_list Uwordbyte
                                                                                                                       (stm_exp (exp_var "ж393"))
                                                                                                                       [
                                                                                                                         existT Kbyte (MkAlt (pat_var "ж371") (stm_exp (exp_false)));
                                                                                                                         existT Kword (MkAlt (pat_var "w2") (stm_exp (((exp_var "w1") = (exp_var "w2")))))
                                                                                                                       ]
                                                                                                                       Logic.I))
                                                        ]
                                                        Logic.I)).
    
    (*
      Extended type
        parameter b1
          bool($0)
        parameter b2
          bool($1)
        return value
          "not('ex12426#)" && $1 || $0 && "not('ex12427#)"
    *)
    Definition fun_xor_bool : Stm [
                                    "b1"  ∷  ty.bool;
                                    "b2"  ∷  ty.bool
                                  ]
                                  (ty.bool) :=
      stm_let "ga#71"
              (ty.bool)
              (stm_let "ga#70"
                       (ty.bool)
                       (stm_exp (exp_unop uop.not (exp_var "b1")))
                       (stm_let "ж394"
                                (ty.bool)
                                (stm_exp (exp_var "ga#70"))
                                (stm_if ((stm_exp (exp_var "ж394")))
                                        (stm_exp (exp_var "b2"))
                                        (stm_exp (exp_false)))))
              (stm_let "ж396"
                       (ty.bool)
                       (stm_exp (exp_var "ga#71"))
                       (stm_if ((stm_exp (exp_var "ж396")))
                               (stm_exp (exp_true))
                               (stm_let "ж395"
                                        (ty.bool)
                                        (stm_exp (exp_var "b1"))
                                        (stm_if ((stm_exp (exp_var "ж395")))
                                                (stm_exp (exp_unop uop.not (exp_var "b2")))
                                                (stm_exp (exp_false)))))).
    
    (*
      Extended type
        parameter w
          WordByte
        return value
          ?[12]
      
      [0] : Sail type: {('ex12428# : Int), true. bool('ex12428# < 0)}
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 455
            Sail position: UnknownLocation
    *)
    Definition fun_isNegative : Stm [
                                      "w"  ∷  ty.union Uwordbyte
                                    ]
                                    (ty.bool) :=
      stm_let "ga#72"
              (ty.int)
              (stm_call signedWb (env.snoc (env.nil)
                                           (_::_)
                                           ((exp_var "w"))%exp))
              (stm_exp (((exp_var "ga#72"))<((exp_int 0%Z)))).
    
    (*
      Extended type
        parameter w
          WordByte
        return value
          ?[13]
      
      [0] : Sail type: {('ex12432# : Int), true. bool('ex12432# == 0)}
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 455
            Sail position: UnknownLocation
    *)
    Definition fun_isZero : Stm [
                                  "w"  ∷  ty.union Uwordbyte
                                ]
                                (ty.bool) :=
      stm_let "ga#73"
              (ty.int)
              (stm_call signedWb (env.snoc (env.nil)
                                           (_::_)
                                           ((exp_var "w"))%exp))
              (stm_exp (((exp_var "ga#73"))=((exp_int 0%Z)))).
    
    (*
      Extended type
        parameter s
          string
        parameter wb
          WordByte
        return value
          unit
    *)
    Definition fun_printWordByte : Stm [
                                         "s"  ∷  ty.string;
                                         "wb"  ∷  ty.union Uwordbyte
                                       ]
                                       (ty.unit) :=
      stm_val ty.unit tt.

    (*
      Extended type
        parameter wb
          WordByte
        return value
          string
    *)
    Definition fun_WordByteString : Stm [
                                          "wb"  ∷  ty.union Uwordbyte
                                        ]
                                        (ty.string) :=
      stm_val ty.string "".

    (*
      Extended type
        parameter _ж409
          unit
        return value
          ?[14]
      
      [0] : Sail type: bitvector(((8 - 8) + 1))
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_getOverflowBit : Stm [
                                          "_ж409"  ∷  ty.unit
                                        ]
                                        (ty.bvec (1)) :=
      stm_let "жreg_SRCG1_reg_410"
              (ty.wordBits)
              (stm_read_register SRCG1_reg)
              (stm_exp (exp_unop (uop.vector_subrange 8 1) (exp_var "жreg_SRCG1_reg_410"))).
    
    (*
      Extended type
        parameter b
          ?[15:1]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_setOverflowbitBit : Stm [
                                             "b"  ∷  ty.bvec (1)
                                           ]
                                           (ty.unit) :=
      stm_seq (stm_let "ж411"
                       (ty.wordBits)
                       (stm_let "жreg_SRCG1_reg_412"
                                (ty.wordBits)
                                (stm_read_register SRCG1_reg)
                                (stm_exp (exp_binop (bop.update_vector_subrange 8 1) (exp_var "жreg_SRCG1_reg_412") (exp_var "b"))))
                       (stm_write_register SRCG1_reg (exp_var "ж411")))
              (stm_exp (exp_val (ty.unit) (tt))).
    
    (*
      Extended type
        parameter _ж413
          unit
        return value
          unit
    *)
    Definition fun_setOverflowbitTrue : Stm [
                                              "_ж413"  ∷  ty.unit
                                            ]
                                            (ty.unit) :=
      stm_seq (stm_let "ж414"
                       (ty.wordBits)
                       (stm_let "жreg_SRCG1_reg_415"
                                (ty.wordBits)
                                (stm_read_register SRCG1_reg)
                                (stm_exp (exp_binop (bop.update_vector_subrange 8 1) (exp_var "жreg_SRCG1_reg_415") (exp_val (ty.bvec 1) ([bv 1])))))
                       (stm_write_register SRCG1_reg (exp_var "ж414")))
              (stm_exp (exp_val (ty.unit) (tt))).
    
    (*
      Extended type
        parameter _ж416
          unit
        return value
          unit
    *)
    Definition fun_clearOverflowbit : Stm [
                                            "_ж416"  ∷  ty.unit
                                          ]
                                          (ty.unit) :=
      stm_seq (stm_let "ж417"
                       (ty.wordBits)
                       (stm_let "жreg_SRCG1_reg_418"
                                (ty.wordBits)
                                (stm_read_register SRCG1_reg)
                                (stm_exp (exp_binop (bop.update_vector_subrange 8 1) (exp_var "жreg_SRCG1_reg_418") (exp_val (ty.bvec 1) ([bv 0])))))
                       (stm_write_register SRCG1_reg (exp_var "ж417")))
              (stm_exp (exp_val (ty.unit) (tt))).
    
    (*
      Extended type
        parameter _ж419
          unit
        return value
          $0
    *)
    Definition fun_overflowbitSet : Stm [
                                          "_ж419"  ∷  ty.unit
                                        ]
                                        (ty.bool) :=
      stm_let "ga#74"
              (ty.bvec (1))
              (stm_let "жreg_SRCG1_reg_420"
                       (ty.wordBits)
                       (stm_read_register SRCG1_reg)
                       (stm_exp (exp_unop (uop.vector_subrange 8 1) (exp_var "жreg_SRCG1_reg_420"))))
              (stm_exp (((exp_var "ga#74") = (exp_val (ty.bvec 1) ([bv 1]))))).
    
    (*
      Extended type
        parameter _ж421
          unit
        return value
          ?[16]
      
      [0] : Sail type: bitvector(((2 - 2) + 1))
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_getNegativeBit : Stm [
                                          "_ж421"  ∷  ty.unit
                                        ]
                                        (ty.bvec (1)) :=
      stm_let "жreg_SRCG1_reg_422"
              (ty.wordBits)
              (stm_read_register SRCG1_reg)
              (stm_exp (exp_unop (uop.vector_subrange 2 1) (exp_var "жreg_SRCG1_reg_422"))).
    
    (*
      Extended type
        parameter b
          ?[17:1]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_setNegativebitBit : Stm [
                                             "b"  ∷  ty.bvec (1)
                                           ]
                                           (ty.unit) :=
      stm_seq (stm_let "ж423"
                       (ty.wordBits)
                       (stm_let "жreg_SRCG1_reg_424"
                                (ty.wordBits)
                                (stm_read_register SRCG1_reg)
                                (stm_exp (exp_binop (bop.update_vector_subrange 2 1) (exp_var "жreg_SRCG1_reg_424") (exp_var "b"))))
                       (stm_write_register SRCG1_reg (exp_var "ж423")))
              (stm_exp (exp_val (ty.unit) (tt))).
    
    (*
      Extended type
        parameter _ж425
          unit
        return value
          unit
    *)
    Definition fun_setNegativebitTrue : Stm [
                                              "_ж425"  ∷  ty.unit
                                            ]
                                            (ty.unit) :=
      stm_seq (stm_let "ж426"
                       (ty.wordBits)
                       (stm_let "жreg_SRCG1_reg_427"
                                (ty.wordBits)
                                (stm_read_register SRCG1_reg)
                                (stm_exp (exp_binop (bop.update_vector_subrange 2 1) (exp_var "жreg_SRCG1_reg_427") (exp_val (ty.bvec 1) ([bv 1])))))
                       (stm_write_register SRCG1_reg (exp_var "ж426")))
              (stm_exp (exp_val (ty.unit) (tt))).
    
    (*
      Extended type
        parameter _ж428
          unit
        return value
          unit
    *)
    Definition fun_clearNegativebit : Stm [
                                            "_ж428"  ∷  ty.unit
                                          ]
                                          (ty.unit) :=
      stm_seq (stm_let "ж429"
                       (ty.wordBits)
                       (stm_let "жreg_SRCG1_reg_430"
                                (ty.wordBits)
                                (stm_read_register SRCG1_reg)
                                (stm_exp (exp_binop (bop.update_vector_subrange 2 1) (exp_var "жreg_SRCG1_reg_430") (exp_val (ty.bvec 1) ([bv 0])))))
                       (stm_write_register SRCG1_reg (exp_var "ж429")))
              (stm_exp (exp_val (ty.unit) (tt))).
    
    (*
      Extended type
        parameter _ж431
          unit
        return value
          $0
    *)
    Definition fun_negativebitSet : Stm [
                                          "_ж431"  ∷  ty.unit
                                        ]
                                        (ty.bool) :=
      stm_let "ga#75"
              (ty.bvec (1))
              (stm_let "жreg_SRCG1_reg_432"
                       (ty.wordBits)
                       (stm_read_register SRCG1_reg)
                       (stm_exp (exp_unop (uop.vector_subrange 2 1) (exp_var "жreg_SRCG1_reg_432"))))
              (stm_exp (((exp_var "ga#75") = (exp_val (ty.bvec 1) ([bv 1]))))).
    
    (*
      Extended type
        parameter _ж433
          unit
        return value
          ?[18]
      
      [0] : Sail type: bitvector(((1 - 1) + 1))
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_getZeroBit : Stm [
                                      "_ж433"  ∷  ty.unit
                                    ]
                                    (ty.bvec (1)) :=
      stm_let "жreg_SRCG1_reg_434"
              (ty.wordBits)
              (stm_read_register SRCG1_reg)
              (stm_exp (exp_unop (uop.vector_subrange 1 1) (exp_var "жreg_SRCG1_reg_434"))).
    
    (*
      Extended type
        parameter b
          ?[19:1]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_setZerobitBit : Stm [
                                         "b"  ∷  ty.bvec (1)
                                       ]
                                       (ty.unit) :=
      stm_seq (stm_let "ж435"
                       (ty.wordBits)
                       (stm_let "жreg_SRCG1_reg_436"
                                (ty.wordBits)
                                (stm_read_register SRCG1_reg)
                                (stm_exp (exp_binop (bop.update_vector_subrange 1 1) (exp_var "жreg_SRCG1_reg_436") (exp_var "b"))))
                       (stm_write_register SRCG1_reg (exp_var "ж435")))
              (stm_exp (exp_val (ty.unit) (tt))).
    
    (*
      Extended type
        parameter _ж437
          unit
        return value
          unit
    *)
    Definition fun_setZerobitTrue : Stm [
                                          "_ж437"  ∷  ty.unit
                                        ]
                                        (ty.unit) :=
      stm_seq (stm_let "ж438"
                       (ty.wordBits)
                       (stm_let "жreg_SRCG1_reg_439"
                                (ty.wordBits)
                                (stm_read_register SRCG1_reg)
                                (stm_exp (exp_binop (bop.update_vector_subrange 1 1) (exp_var "жreg_SRCG1_reg_439") (exp_val (ty.bvec 1) ([bv 1])))))
                       (stm_write_register SRCG1_reg (exp_var "ж438")))
              (stm_exp (exp_val (ty.unit) (tt))).
    
    (*
      Extended type
        parameter _ж440
          unit
        return value
          unit
    *)
    Definition fun_clearZerobit : Stm [
                                        "_ж440"  ∷  ty.unit
                                      ]
                                      (ty.unit) :=
      stm_seq (stm_let "ж441"
                       (ty.wordBits)
                       (stm_let "жreg_SRCG1_reg_442"
                                (ty.wordBits)
                                (stm_read_register SRCG1_reg)
                                (stm_exp (exp_binop (bop.update_vector_subrange 1 1) (exp_var "жreg_SRCG1_reg_442") (exp_val (ty.bvec 1) ([bv 0])))))
                       (stm_write_register SRCG1_reg (exp_var "ж441")))
              (stm_exp (exp_val (ty.unit) (tt))).
    
    (*
      Extended type
        parameter _ж443
          unit
        return value
          $0
    *)
    Definition fun_zerobitSet : Stm [
                                      "_ж443"  ∷  ty.unit
                                    ]
                                    (ty.bool) :=
      stm_let "ga#76"
              (ty.bvec (1))
              (stm_let "жreg_SRCG1_reg_444"
                       (ty.wordBits)
                       (stm_read_register SRCG1_reg)
                       (stm_exp (exp_unop (uop.vector_subrange 1 1) (exp_var "жreg_SRCG1_reg_444"))))
              (stm_exp (((exp_var "ga#76") = (exp_val (ty.bvec 1) ([bv 1]))))).
    
    (*
      Extended type
        parameter _ж445
          unit
        return value
          ?[20]
      
      [0] : Sail type: bitvector(((0 - 0) + 1))
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_getCarryBit : Stm [
                                       "_ж445"  ∷  ty.unit
                                     ]
                                     (ty.bvec (1)) :=
      stm_let "жreg_SRCG1_reg_446"
              (ty.wordBits)
              (stm_read_register SRCG1_reg)
              (stm_exp (exp_unop (uop.vector_subrange 0 1) (exp_var "жreg_SRCG1_reg_446"))).
    
    (*
      Extended type
        parameter b
          ?[21:1]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_setCarrybitBit : Stm [
                                          "b"  ∷  ty.bvec (1)
                                        ]
                                        (ty.unit) :=
      stm_seq (stm_let "ж447"
                       (ty.wordBits)
                       (stm_let "жreg_SRCG1_reg_448"
                                (ty.wordBits)
                                (stm_read_register SRCG1_reg)
                                (stm_exp (exp_binop (bop.update_vector_subrange 0 1) (exp_var "жreg_SRCG1_reg_448") (exp_var "b"))))
                       (stm_write_register SRCG1_reg (exp_var "ж447")))
              (stm_exp (exp_val (ty.unit) (tt))).
    
    (*
      Extended type
        parameter _ж449
          unit
        return value
          unit
    *)
    Definition fun_setCarrybitTrue : Stm [
                                           "_ж449"  ∷  ty.unit
                                         ]
                                         (ty.unit) :=
      stm_seq (stm_let "ж450"
                       (ty.wordBits)
                       (stm_let "жreg_SRCG1_reg_451"
                                (ty.wordBits)
                                (stm_read_register SRCG1_reg)
                                (stm_exp (exp_binop (bop.update_vector_subrange 0 1) (exp_var "жreg_SRCG1_reg_451") (exp_val (ty.bvec 1) ([bv 1])))))
                       (stm_write_register SRCG1_reg (exp_var "ж450")))
              (stm_exp (exp_val (ty.unit) (tt))).
    
    (*
      Extended type
        parameter _ж452
          unit
        return value
          unit
    *)
    Definition fun_clearCarrybit : Stm [
                                         "_ж452"  ∷  ty.unit
                                       ]
                                       (ty.unit) :=
      stm_seq (stm_let "ж453"
                       (ty.wordBits)
                       (stm_let "жreg_SRCG1_reg_454"
                                (ty.wordBits)
                                (stm_read_register SRCG1_reg)
                                (stm_exp (exp_binop (bop.update_vector_subrange 0 1) (exp_var "жreg_SRCG1_reg_454") (exp_val (ty.bvec 1) ([bv 0])))))
                       (stm_write_register SRCG1_reg (exp_var "ж453")))
              (stm_exp (exp_val (ty.unit) (tt))).
    
    (*
      Extended type
        parameter _ж455
          unit
        return value
          $0
    *)
    Definition fun_carrybitSet : Stm [
                                       "_ж455"  ∷  ty.unit
                                     ]
                                     (ty.bool) :=
      stm_let "ga#77"
              (ty.bvec (1))
              (stm_let "жreg_SRCG1_reg_456"
                       (ty.wordBits)
                       (stm_read_register SRCG1_reg)
                       (stm_exp (exp_unop (uop.vector_subrange 0 1) (exp_var "жreg_SRCG1_reg_456"))))
              (stm_exp (((exp_var "ga#77") = (exp_val (ty.bvec 1) ([bv 1]))))).
    
    (*
      Extended type
        parameter _ж457
          unit
        return value
          unit
    *)
    Definition fun_setAllStatusbits : Stm [
                                            "_ж457"  ∷  ty.unit
                                          ]
                                          (ty.unit) :=
      stm_seq (stm_call setCarrybitTrue (env.snoc (env.nil)
                                                  (_::_)
                                                  ((exp_val (ty.unit) (tt)))%exp))
              (stm_seq (stm_call setNegativebitTrue (env.snoc (env.nil)
                                                              (_::_)
                                                              ((exp_val (ty.unit) (tt)))%exp))
                       (stm_seq (stm_call setZerobitTrue (env.snoc (env.nil)
                                                                   (_::_)
                                                                   ((exp_val (ty.unit) (tt)))%exp))
                                (stm_call setOverflowbitTrue (env.snoc (env.nil)
                                                                       (_::_)
                                                                       ((exp_val (ty.unit) (tt)))%exp)))).
    
    (*
      Extended type
        parameter _ж467
          unit
        return value
          unit
    *)
    Definition fun_clearStatusRegisters : Stm [
                                                "_ж467"  ∷  ty.unit
                                              ]
                                              (ty.unit) :=
      stm_seq (stm_call clearNegativebit (env.snoc (env.nil)
                                                   (_::_)
                                                   ((exp_val (ty.unit) (tt)))%exp))
              (stm_seq (stm_call clearCarrybit (env.snoc (env.nil)
                                                         (_::_)
                                                         ((exp_val (ty.unit) (tt)))%exp))
                       (stm_seq (stm_call clearOverflowbit (env.snoc (env.nil)
                                                                     (_::_)
                                                                     ((exp_val (ty.unit) (tt)))%exp))
                                (stm_call clearZerobit (env.snoc (env.nil)
                                                                 (_::_)
                                                                 ((exp_val (ty.unit) (tt)))%exp)))).
    
    (*
      Extended type
        parameter res
          WordByte
        return value
          unit
    *)
    Definition fun_setResultStatusRegisters : Stm [
                                                    "res"  ∷  ty.union Uwordbyte
                                                  ]
                                                  (ty.unit) :=
      stm_seq (stm_let "ga#84"
                       (ty.bool)
                       (stm_call isNegative (env.snoc (env.nil)
                                                      (_::_)
                                                      ((exp_var "res"))%exp))
                       (stm_let "ж477"
                                (ty.bool)
                                (stm_exp (exp_var "ga#84"))
                                (stm_if ((stm_exp (exp_var "ж477")))
                                        (stm_call setNegativebitTrue (env.snoc (env.nil)
                                                                               (_::_)
                                                                               ((exp_val (ty.unit) (tt)))%exp))
                                        (stm_exp (exp_val (ty.unit) (tt))))))
              (stm_let "ga#86"
                       (ty.bool)
                       (stm_call isZero (env.snoc (env.nil)
                                                  (_::_)
                                                  ((exp_var "res"))%exp))
                       (stm_let "ж479"
                                (ty.bool)
                                (stm_exp (exp_var "ga#86"))
                                (stm_if ((stm_exp (exp_var "ж479")))
                                        (stm_call setZerobitTrue (env.snoc (env.nil)
                                                                           (_::_)
                                                                           ((exp_val (ty.unit) (tt)))%exp))
                                        (stm_exp (exp_val (ty.unit) (tt)))))).
    
    (*
      Extended type
        parameter arg#
          mpu_register_name
        return value
          ?[22]
      
      [0] : Sail type: range(0, 7)
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: ../msp430-ipe-sail/_compilation/mpu.sail:11
    *)
    Definition fun_mpu_register_index_forwards : Stm [
                                                       "arg#"  ∷  ty.enum Empu_register_name
                                                     ]
                                                     (ty.int) :=
      stm_let "ж482"
              (ty.enum Empu_register_name)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Empu_register_name
                              (stm_exp (exp_var "ж482"))
                              (fun K => match K with
                                        | MPUCTL0    => stm_exp (exp_int 0%Z)
                                        | MPUCTL1    => stm_exp (exp_int 1%Z)
                                        | MPUIPC0    => stm_exp (exp_int 5%Z)
                                        | MPUIPSEGB1 => stm_exp (exp_int 7%Z)
                                        | MPUIPSEGB2 => stm_exp (exp_int 6%Z)
                                        | MPUSAM     => stm_exp (exp_int 4%Z)
                                        | MPUSEGB1   => stm_exp (exp_int 3%Z)
                                        | MPUSEGB2   => stm_exp (exp_int 2%Z)
                                        end)).
    
    (*
      Extended type
        parameter arg#
          int($0)
        return value
          mpu_register_name
    *)
    Definition fun_mpu_register_index_backwards : Stm [
                                                        "arg#"  ∷  ty.int
                                                      ]
                                                      (ty.enum Empu_register_name) :=
      stm_let "l__10"
              (ty.int)
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#87"
                       (ty.bool)
                       (stm_exp (((exp_var "l__10"))=((exp_int 0%Z))))
                       (stm_let "ж498"
                                (ty.bool)
                                (stm_exp (exp_var "ga#87"))
                                (stm_if ((stm_exp (exp_var "ж498")))
                                        (stm_exp (exp_val (ty.enum Empu_register_name) (MPUCTL0)))
                                        (stm_let "ga#88"
                                                 (ty.bool)
                                                 (stm_exp (((exp_var "l__10"))=((exp_int 1%Z))))
                                                 (stm_let "ж497"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#88"))
                                                          (stm_if ((stm_exp (exp_var "ж497")))
                                                                  (stm_exp (exp_val (ty.enum Empu_register_name) (MPUCTL1)))
                                                                  (stm_let "ga#89"
                                                                           (ty.bool)
                                                                           (stm_exp (((exp_var "l__10"))=((exp_int 2%Z))))
                                                                           (stm_let "ж496"
                                                                                    (ty.bool)
                                                                                    (stm_exp (exp_var "ga#89"))
                                                                                    (stm_if ((stm_exp (exp_var "ж496")))
                                                                                            (stm_exp (exp_val (ty.enum Empu_register_name) (MPUSEGB2)))
                                                                                            (stm_let "ga#90"
                                                                                                     (ty.bool)
                                                                                                     (stm_exp (((exp_var "l__10"))=((exp_int 3%Z))))
                                                                                                     (stm_let "ж495"
                                                                                                              (ty.bool)
                                                                                                              (stm_exp (exp_var "ga#90"))
                                                                                                              (stm_if ((stm_exp (exp_var "ж495")))
                                                                                                                      (stm_exp (exp_val (ty.enum Empu_register_name) (MPUSEGB1)))
                                                                                                                      (stm_let "ga#91"
                                                                                                                               (ty.bool)
                                                                                                                               (stm_exp (((exp_var "l__10"))=((exp_int 4%Z))))
                                                                                                                               (stm_let "ж494"
                                                                                                                                        (ty.bool)
                                                                                                                                        (stm_exp (exp_var "ga#91"))
                                                                                                                                        (stm_if ((stm_exp (exp_var "ж494")))
                                                                                                                                                (stm_exp (exp_val (ty.enum Empu_register_name) (MPUSAM)))
                                                                                                                                                (stm_let "ga#92"
                                                                                                                                                         (ty.bool)
                                                                                                                                                         (stm_exp (((exp_var "l__10"))=((exp_int 5%Z))))
                                                                                                                                                         (stm_let "ж493"
                                                                                                                                                                  (ty.bool)
                                                                                                                                                                  (stm_exp (exp_var "ga#92"))
                                                                                                                                                                  (stm_if ((stm_exp (exp_var "ж493")))
                                                                                                                                                                          (stm_exp (exp_val (ty.enum Empu_register_name) (MPUIPC0)))
                                                                                                                                                                          (stm_let "ga#93"
                                                                                                                                                                                   (ty.bool)
                                                                                                                                                                                   (stm_exp (((exp_var "l__10"))=((exp_int 6%Z))))
                                                                                                                                                                                   (stm_let "ж492"
                                                                                                                                                                                            (ty.bool)
                                                                                                                                                                                            (stm_exp (exp_var "ga#93"))
                                                                                                                                                                                            (stm_if ((stm_exp (exp_var "ж492")))
                                                                                                                                                                                                    (stm_exp (exp_val (ty.enum Empu_register_name) (MPUIPSEGB2)))
                                                                                                                                                                                                    (stm_exp (exp_val (ty.enum Empu_register_name) (MPUIPSEGB1)))))))))))))))))))))))).
    
    (*
      Extended type
        parameter arg#
          mpu_register_name
        return value
          $0
    *)
    Definition fun_mpu_register_index_forwards_matches : Stm [
                                                               "arg#"  ∷  ty.enum Empu_register_name
                                                             ]
                                                             (ty.bool) :=
      stm_let "ж499"
              (ty.enum Empu_register_name)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Empu_register_name
                              (stm_exp (exp_var "ж499"))
                              (fun K => match K with
                                        | MPUCTL0    => stm_exp (exp_true)
                                        | MPUCTL1    => stm_exp (exp_true)
                                        | MPUIPC0    => stm_exp (exp_true)
                                        | MPUIPSEGB1 => stm_exp (exp_true)
                                        | MPUIPSEGB2 => stm_exp (exp_true)
                                        | MPUSAM     => stm_exp (exp_true)
                                        | MPUSEGB1   => stm_exp (exp_true)
                                        | MPUSEGB2   => stm_exp (exp_true)
                                        end)).
    
    (*
      Extended type
        parameter arg#
          int($0)
        return value
          $1
    *)
    Definition fun_mpu_register_index_backwards_matches : Stm [
                                                                "arg#"  ∷  ty.int
                                                              ]
                                                              (ty.bool) :=
      stm_let "l__2"
              (ty.int)
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#94"
                       (ty.bool)
                       (stm_exp (((exp_var "l__2"))=((exp_int 0%Z))))
                       (stm_let "ж516"
                                (ty.bool)
                                (stm_exp (exp_var "ga#94"))
                                (stm_if ((stm_exp (exp_var "ж516")))
                                        (stm_exp (exp_true))
                                        (stm_let "ga#95"
                                                 (ty.bool)
                                                 (stm_exp (((exp_var "l__2"))=((exp_int 1%Z))))
                                                 (stm_let "ж515"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#95"))
                                                          (stm_if ((stm_exp (exp_var "ж515")))
                                                                  (stm_exp (exp_true))
                                                                  (stm_let "ga#96"
                                                                           (ty.bool)
                                                                           (stm_exp (((exp_var "l__2"))=((exp_int 2%Z))))
                                                                           (stm_let "ж514"
                                                                                    (ty.bool)
                                                                                    (stm_exp (exp_var "ga#96"))
                                                                                    (stm_if ((stm_exp (exp_var "ж514")))
                                                                                            (stm_exp (exp_true))
                                                                                            (stm_let "ga#97"
                                                                                                     (ty.bool)
                                                                                                     (stm_exp (((exp_var "l__2"))=((exp_int 3%Z))))
                                                                                                     (stm_let "ж513"
                                                                                                              (ty.bool)
                                                                                                              (stm_exp (exp_var "ga#97"))
                                                                                                              (stm_if ((stm_exp (exp_var "ж513")))
                                                                                                                      (stm_exp (exp_true))
                                                                                                                      (stm_let "ga#98"
                                                                                                                               (ty.bool)
                                                                                                                               (stm_exp (((exp_var "l__2"))=((exp_int 4%Z))))
                                                                                                                               (stm_let "ж512"
                                                                                                                                        (ty.bool)
                                                                                                                                        (stm_exp (exp_var "ga#98"))
                                                                                                                                        (stm_if ((stm_exp (exp_var "ж512")))
                                                                                                                                                (stm_exp (exp_true))
                                                                                                                                                (stm_let "ga#99"
                                                                                                                                                         (ty.bool)
                                                                                                                                                         (stm_exp (((exp_var "l__2"))=((exp_int 5%Z))))
                                                                                                                                                         (stm_let "ж511"
                                                                                                                                                                  (ty.bool)
                                                                                                                                                                  (stm_exp (exp_var "ga#99"))
                                                                                                                                                                  (stm_if ((stm_exp (exp_var "ж511")))
                                                                                                                                                                          (stm_exp (exp_true))
                                                                                                                                                                          (stm_let "ga#100"
                                                                                                                                                                                   (ty.bool)
                                                                                                                                                                                   (stm_exp (((exp_var "l__2"))=((exp_int 6%Z))))
                                                                                                                                                                                   (stm_let "ж510"
                                                                                                                                                                                            (ty.bool)
                                                                                                                                                                                            (stm_exp (exp_var "ga#100"))
                                                                                                                                                                                            (stm_if ((stm_exp (exp_var "ж510")))
                                                                                                                                                                                                    (stm_exp (exp_true))
                                                                                                                                                                                                    (stm_let "ga#101"
                                                                                                                                                                                                             (ty.bool)
                                                                                                                                                                                                             (stm_exp (((exp_var "l__2"))=((exp_int 7%Z))))
                                                                                                                                                                                                             (stm_let "ж509"
                                                                                                                                                                                                                      (ty.bool)
                                                                                                                                                                                                                      (stm_exp (exp_var "ga#101"))
                                                                                                                                                                                                                      (stm_if ((stm_exp (exp_var "ж509")))
                                                                                                                                                                                                                              (stm_exp (exp_true))
                                                                                                                                                                                                                              (stm_exp (exp_false)))))))))))))))))))))))))).
    
    (*
      Extended type
        parameter addr
          ?[23:16]
        return value
          $0
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_is_mpu_reg_addr : Stm [
                                           "addr"  ∷  ty.bvec (16)
                                         ]
                                         (ty.bool) :=
      stm_let "off"
              (ty.int)
              (stm_let "ga#103"
                       (ty.int)
                       (stm_exp (exp_unop uop.unsigned (exp_var "addr")))
                       (stm_let "ga#104"
                                (ty.int)
                                (stm_exp (exp_unop uop.unsigned (exp_val (ty.bvec 16) ([bv 1440]))))
                                (stm_exp (((exp_var "ga#103"))-((exp_var "ga#104"))))))
              (stm_let "ga#102"
                       (ty.bool)
                       (stm_exp (((exp_var "off"))>=((exp_int 0%Z))))
                       (stm_let "ж517"
                                (ty.bool)
                                (stm_exp (exp_var "ga#102"))
                                (stm_if ((stm_exp (exp_var "ж517")))
                                        (stm_exp (((exp_var "off"))<((exp_int 16%Z))))
                                        (stm_exp (exp_false))))).
    
    (*
      Extended type
        parameter addr
          ?[24:16]
        return value
          ?[25]
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
      
      [1] : Sail type: bitvector(8)
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_read_mpu_reg_byte : Stm [
                                             "addr"  ∷  ty.bvec (16)
                                           ]
                                           (ty.bvec (8)) :=
      stm_let "idx"
              (ty.int)
              (stm_let "ga#114"
                       (ty.int)
                       (stm_let "ga#112"
                                (ty.bvec (16))
                                (stm_call shiftr (env.snoc (env.snoc (env.nil)
                                                                     (_::_)
                                                                     ((exp_var "addr"))%exp)
                                                           (_::_)
                                                           ((exp_int 1%Z))%exp))
                                (stm_exp (exp_unop uop.unsigned (exp_var "ga#112"))))
                       (stm_let "ga#115"
                                (ty.int)
                                (stm_let "ga#113"
                                         (ty.bvec (16))
                                         (stm_call shiftr (env.snoc (env.snoc (env.nil)
                                                                              (_::_)
                                                                              ((exp_val (ty.bvec 16) ([bv 1440])))%exp)
                                                                    (_::_)
                                                                    ((exp_int 1%Z))%exp))
                                         (stm_exp (exp_unop uop.unsigned (exp_var "ga#113"))))
                                (stm_exp (((exp_var "ga#114"))-((exp_var "ga#115"))))))
              (stm_let "ga#106"
                       (ty.bool)
                       (stm_let "ga#105"
                                (ty.bool)
                                (stm_exp (((exp_var "idx"))>=((exp_int 0%Z))))
                                (stm_let "ж518"
                                         (ty.bool)
                                         (stm_exp (exp_var "ga#105"))
                                         (stm_if ((stm_exp (exp_var "ж518")))
                                                 (stm_exp (((exp_var "idx"))<((exp_int 8%Z))))
                                                 (stm_exp (exp_false)))))
                       (stm_let "ж541"
                                (ty.bool)
                                (stm_exp (exp_var "ga#106"))
                                (stm_if ((stm_exp (exp_var "ж541")))
                                        (stm_let "w"
                                                 (ty.wordBits)
                                                 (stm_let "ga#108"
                                                          (ty.enum Empu_register_name)
                                                          (stm_call mpu_register_index_backwards (env.snoc (env.nil)
                                                                                                           (_::_)
                                                                                                           ((exp_var "idx"))%exp))
                                                          (stm_let "ж519"
                                                                   (ty.enum Empu_register_name)
                                                                   (stm_exp (exp_var "ga#108"))
                                                                   (stm_match_enum Empu_register_name
                                                                                   (stm_exp (exp_var "ж519"))
                                                                                   (fun K => match K with
                                                                                             | MPUCTL0    => stm_let "ga#110"
                                                                                                                     (ty.bvec (16))
                                                                                                                     (stm_let "ga#109"
                                                                                                                              (ty.bvec (16))
                                                                                                                              (stm_let "жreg_MPUCTL0_reg_520"
                                                                                                                                       (ty.wordBits)
                                                                                                                                       (stm_read_register MPUCTL0_reg)
                                                                                                                                       (stm_exp (exp_binop bop.bvand (exp_var "жreg_MPUCTL0_reg_520") (exp_val (ty.bvec 16) ([bv 255])))))
                                                                                                                              (stm_exp (exp_binop bop.bvor (exp_var "ga#109") (exp_val (ty.bvec 16) ([bv 38400])))))
                                                                                                                     (stm_exp (exp_binop bop.bvand (exp_var "ga#110") (exp_val (ty.bvec 16) ([bv 65299]))))
                                                                                             | MPUCTL1    => stm_let "жreg_MPUCTL1_reg_521"
                                                                                                                     (ty.wordBits)
                                                                                                                     (stm_read_register MPUCTL1_reg)
                                                                                                                     (stm_exp (exp_binop bop.bvand (exp_var "жreg_MPUCTL1_reg_521") (exp_val (ty.bvec 16) ([bv 31]))))
                                                                                             | MPUIPC0    => stm_let "жreg_MPUIPC0_reg_525"
                                                                                                                     (ty.wordBits)
                                                                                                                     (stm_read_register MPUIPC0_reg)
                                                                                                                     (stm_exp (exp_binop bop.bvand (exp_var "жreg_MPUIPC0_reg_525") (exp_val (ty.bvec 16) ([bv 224]))))
                                                                                             | MPUIPSEGB1 => stm_let "жreg_MPUIPSEGB1_reg_527"
                                                                                                                     (ty.wordBits)
                                                                                                                     (stm_read_register MPUIPSEGB1_reg)
                                                                                                                     (stm_exp (exp_var "жreg_MPUIPSEGB1_reg_527"))
                                                                                             | MPUIPSEGB2 => stm_let "жreg_MPUIPSEGB2_reg_526"
                                                                                                                     (ty.wordBits)
                                                                                                                     (stm_read_register MPUIPSEGB2_reg)
                                                                                                                     (stm_exp (exp_var "жreg_MPUIPSEGB2_reg_526"))
                                                                                             | MPUSAM     => stm_let "жreg_MPUSAM_reg_524"
                                                                                                                     (ty.wordBits)
                                                                                                                     (stm_read_register MPUSAM_reg)
                                                                                                                     (stm_exp (exp_var "жreg_MPUSAM_reg_524"))
                                                                                             | MPUSEGB1   => stm_let "жreg_MPUSEGB1_reg_523"
                                                                                                                     (ty.wordBits)
                                                                                                                     (stm_read_register MPUSEGB1_reg)
                                                                                                                     (stm_exp (exp_var "жreg_MPUSEGB1_reg_523"))
                                                                                             | MPUSEGB2   => stm_let "жreg_MPUSEGB2_reg_522"
                                                                                                                     (ty.wordBits)
                                                                                                                     (stm_read_register MPUSEGB2_reg)
                                                                                                                     (stm_exp (exp_var "жreg_MPUSEGB2_reg_522"))
                                                                                             end))))
                                                 (stm_let "b__0"
                                                          (ty.bvec (1))
                                                          (stm_exp (exp_unop (uop.vector_subrange 0 1) (exp_var "addr")))
                                                          (stm_let "ga#107"
                                                                   (ty.bool)
                                                                   (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 1) ([bv 0])))))
                                                                   (stm_let "ж537"
                                                                            (ty.bool)
                                                                            (stm_exp (exp_var "ga#107"))
                                                                            (stm_if ((stm_exp (exp_var "ж537")))
                                                                                    (stm_exp (exp_unop (uop.vector_subrange 0 8) (exp_var "w")))
                                                                                    (stm_exp (exp_unop (uop.vector_subrange 8 8) (exp_var "w"))))))))
                                        (stm_seq (stm_assert (exp_false) (exp_string "../msp430-ipe-sail/_compilation/mpu.sail:53.21-53.22"))
                                                 (stm_fail _ "failure"))))).
    
    (*
      Extended type
        parameter reg
          mpu_register_name
        return value
          $0
    *)
    Definition fun_is_lockable_mpu_reg : Stm [
                                               "reg"  ∷  ty.enum Empu_register_name
                                             ]
                                             (ty.bool) :=
      stm_let "ж542"
              (ty.enum Empu_register_name)
              (stm_exp (exp_var "reg"))
              (stm_match_enum Empu_register_name
                              (stm_exp (exp_var "ж542"))
                              (fun K => match K with
                                        | MPUCTL0    => stm_exp (exp_true)
                                        | MPUCTL1    => stm_exp (exp_false)
                                        | MPUIPC0    => stm_exp (exp_false)
                                        | MPUIPSEGB1 => stm_exp (exp_false)
                                        | MPUIPSEGB2 => stm_exp (exp_false)
                                        | MPUSAM     => stm_exp (exp_true)
                                        | MPUSEGB1   => stm_exp (exp_true)
                                        | MPUSEGB2   => stm_exp (exp_true)
                                        end)).
    
    (*
      Extended type
        parameter reg
          mpu_register_name
        return value
          $0
    *)
    Definition fun_is_ipe_reg : Stm [
                                      "reg"  ∷  ty.enum Empu_register_name
                                    ]
                                    (ty.bool) :=
      stm_let "ж553"
              (ty.enum Empu_register_name)
              (stm_exp (exp_var "reg"))
              (stm_match_enum Empu_register_name
                              (stm_exp (exp_var "ж553"))
                              (fun K => match K with
                                        | MPUCTL0    => stm_exp (exp_false)
                                        | MPUCTL1    => stm_exp (exp_false)
                                        | MPUIPC0    => stm_exp (exp_true)
                                        | MPUIPSEGB1 => stm_exp (exp_true)
                                        | MPUIPSEGB2 => stm_exp (exp_true)
                                        | MPUSAM     => stm_exp (exp_false)
                                        | MPUSEGB1   => stm_exp (exp_false)
                                        | MPUSEGB2   => stm_exp (exp_false)
                                        end)).
    
    (*
      Extended type
        parameter addr
          ?[26:16]
        parameter v
          ?[27:8]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
      
      [1] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_write_mpu_reg_byte : Stm [
                                              "addr"  ∷  ty.bvec (16);
                                              "v"  ∷  ty.bvec (8)
                                            ]
                                            (ty.unit) :=
      stm_let "idx"
              (ty.int)
              (stm_let "ga#132"
                       (ty.int)
                       (stm_let "ga#130"
                                (ty.bvec (16))
                                (stm_call shiftr (env.snoc (env.snoc (env.nil)
                                                                     (_::_)
                                                                     ((exp_var "addr"))%exp)
                                                           (_::_)
                                                           ((exp_int 1%Z))%exp))
                                (stm_exp (exp_unop uop.unsigned (exp_var "ga#130"))))
                       (stm_let "ga#133"
                                (ty.int)
                                (stm_let "ga#131"
                                         (ty.bvec (16))
                                         (stm_call shiftr (env.snoc (env.snoc (env.nil)
                                                                              (_::_)
                                                                              ((exp_val (ty.bvec 16) ([bv 1440])))%exp)
                                                                    (_::_)
                                                                    ((exp_int 1%Z))%exp))
                                         (stm_exp (exp_unop uop.unsigned (exp_var "ga#131"))))
                                (stm_exp (((exp_var "ga#132"))-((exp_var "ga#133"))))))
              (stm_let "low_byte"
                       (ty.bool)
                       (stm_let "ga#129"
                                (ty.bvec (1))
                                (stm_exp (exp_unop (uop.vector_subrange 0 1) (exp_var "addr")))
                                (stm_exp (((exp_var "ga#129") = (exp_val (ty.bvec 1) ([bv 0]))))))
                       (stm_let "ga#117"
                                (ty.bool)
                                (stm_let "ga#116"
                                         (ty.bool)
                                         (stm_exp (((exp_var "idx"))>=((exp_int 0%Z))))
                                         (stm_let "ж564"
                                                  (ty.bool)
                                                  (stm_exp (exp_var "ga#116"))
                                                  (stm_if ((stm_exp (exp_var "ж564")))
                                                          (stm_exp (((exp_var "idx"))<((exp_int 8%Z))))
                                                          (stm_exp (exp_false)))))
                                (stm_let "ж639"
                                         (ty.bool)
                                         (stm_exp (exp_var "ga#117"))
                                         (stm_if ((stm_exp (exp_var "ж639")))
                                                 (stm_let "reg"
                                                          (ty.enum Empu_register_name)
                                                          (stm_call mpu_register_index_backwards (env.snoc (env.nil)
                                                                                                           (_::_)
                                                                                                           ((exp_var "idx"))%exp))
                                                          (stm_let "reg_is_not_MPUCTL0"
                                                                   (ty.bool)
                                                                   (stm_let "ж565"
                                                                            (ty.enum Empu_register_name)
                                                                            (stm_exp (exp_var "reg"))
                                                                            (stm_match_enum Empu_register_name
                                                                                            (stm_exp (exp_var "ж565"))
                                                                                            (fun K => match K with
                                                                                                      | MPUCTL0    => stm_exp (exp_false)
                                                                                                      | MPUCTL1    => stm_exp (exp_true)
                                                                                                      | MPUIPC0    => stm_exp (exp_true)
                                                                                                      | MPUIPSEGB1 => stm_exp (exp_true)
                                                                                                      | MPUIPSEGB2 => stm_exp (exp_true)
                                                                                                      | MPUSAM     => stm_exp (exp_true)
                                                                                                      | MPUSEGB1   => stm_exp (exp_true)
                                                                                                      | MPUSEGB2   => stm_exp (exp_true)
                                                                                                      end)))
                                                                   (stm_let "ga#121"
                                                                            (ty.bool)
                                                                            (stm_let "ga#120"
                                                                                     (ty.bool)
                                                                                     (stm_let "ga#119"
                                                                                              (ty.bool)
                                                                                              (stm_let "ga#118"
                                                                                                       (ty.bvec (8))
                                                                                                       (stm_let "жreg_MPUCTL0_reg_576"
                                                                                                                (ty.wordBits)
                                                                                                                (stm_read_register MPUCTL0_reg)
                                                                                                                (stm_exp (exp_unop (uop.vector_subrange 8 8) (exp_var "жreg_MPUCTL0_reg_576"))))
                                                                                                       (stm_exp (((exp_var "ga#118") = (exp_val (ty.bvec 8) ([bv 165]))))))
                                                                                              (stm_exp (exp_unop uop.not (exp_var "ga#119"))))
                                                                                     (stm_let "ж578"
                                                                                              (ty.bool)
                                                                                              (stm_exp (exp_var "ga#120"))
                                                                                              (stm_if ((stm_exp (exp_var "ж578")))
                                                                                                      (stm_let "ж577"
                                                                                                               (ty.bool)
                                                                                                               (stm_exp (exp_var "reg_is_not_MPUCTL0"))
                                                                                                               (stm_if ((stm_exp (exp_var "ж577")))
                                                                                                                       (stm_exp (exp_true))
                                                                                                                       (stm_exp (exp_var "low_byte"))))
                                                                                                      (stm_exp (exp_false)))))
                                                                            (stm_let "ж638"
                                                                                     (ty.bool)
                                                                                     (stm_exp (exp_var "ga#121"))
                                                                                     (stm_if ((stm_exp (exp_var "ж638")))
                                                                                             (stm_seq (stm_exp (exp_union Uexception Kpower_up_clear (exp_val (ty.unit) (tt))))
                                                                                                      (stm_fail _ "failure"))
                                                                                             (stm_let "ga#128"
                                                                                                      (ty.bool)
                                                                                                      (stm_let "ga#127"
                                                                                                               (ty.bool)
                                                                                                               (stm_let "ga#124"
                                                                                                                        (ty.bool)
                                                                                                                        (stm_call is_lockable_mpu_reg (env.snoc (env.nil)
                                                                                                                                                                (_::_)
                                                                                                                                                                ((exp_var "reg"))%exp))
                                                                                                                        (stm_let "ж580"
                                                                                                                                 (ty.bool)
                                                                                                                                 (stm_exp (exp_var "ga#124"))
                                                                                                                                 (stm_if ((stm_exp (exp_var "ж580")))
                                                                                                                                         (stm_let "ga#123"
                                                                                                                                                  (ty.bvec (1))
                                                                                                                                                  (stm_let "жreg_MPUCTL0_reg_579"
                                                                                                                                                           (ty.wordBits)
                                                                                                                                                           (stm_read_register MPUCTL0_reg)
                                                                                                                                                           (stm_exp (exp_unop (uop.vector_subrange 1 1) (exp_var "жreg_MPUCTL0_reg_579"))))
                                                                                                                                                  (stm_exp (((exp_var "ga#123") = (exp_val (ty.bvec 1) ([bv 1]))))))
                                                                                                                                         (stm_exp (exp_false)))))
                                                                                                               (stm_let "ж583"
                                                                                                                        (ty.bool)
                                                                                                                        (stm_exp (exp_var "ga#127"))
                                                                                                                        (stm_if ((stm_exp (exp_var "ж583")))
                                                                                                                                (stm_exp (exp_true))
                                                                                                                                (stm_let "ga#126"
                                                                                                                                         (ty.bool)
                                                                                                                                         (stm_call is_ipe_reg (env.snoc (env.nil)
                                                                                                                                                                        (_::_)
                                                                                                                                                                        ((exp_var "reg"))%exp))
                                                                                                                                         (stm_let "ж582"
                                                                                                                                                  (ty.bool)
                                                                                                                                                  (stm_exp (exp_var "ga#126"))
                                                                                                                                                  (stm_if ((stm_exp (exp_var "ж582")))
                                                                                                                                                          (stm_let "ga#125"
                                                                                                                                                                   (ty.bvec (1))
                                                                                                                                                                   (stm_let "жreg_MPUIPC0_reg_581"
                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                            (stm_read_register MPUIPC0_reg)
                                                                                                                                                                            (stm_exp (exp_unop (uop.vector_subrange 7 1) (exp_var "жreg_MPUIPC0_reg_581"))))
                                                                                                                                                                   (stm_exp (((exp_var "ga#125") = (exp_val (ty.bvec 1) ([bv 1]))))))
                                                                                                                                                          (stm_exp (exp_false))))))))
                                                                                                      (stm_let "ж637"
                                                                                                               (ty.bool)
                                                                                                               (stm_exp (exp_var "ga#128"))
                                                                                                               (stm_if ((stm_exp (exp_var "ж637")))
                                                                                                                       (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                       (stm_let "ж636"
                                                                                                                                (ty.bool)
                                                                                                                                (stm_exp (exp_var "low_byte"))
                                                                                                                                (stm_if ((stm_exp (exp_var "ж636")))
                                                                                                                                        (stm_let "ж584"
                                                                                                                                                 (ty.enum Empu_register_name)
                                                                                                                                                 (stm_exp (exp_var "reg"))
                                                                                                                                                 (stm_match_enum Empu_register_name
                                                                                                                                                                 (stm_exp (exp_var "ж584"))
                                                                                                                                                                 (fun K => match K with
                                                                                                                                                                           | MPUCTL0    => stm_seq (stm_let "ж585"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUCTL0_reg_586"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUCTL0_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 0 8) (exp_var "жreg_MPUCTL0_reg_586") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUCTL0_reg (exp_var "ж585")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           | MPUCTL1    => stm_seq (stm_let "ж587"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUCTL1_reg_588"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUCTL1_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 0 8) (exp_var "жreg_MPUCTL1_reg_588") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUCTL1_reg (exp_var "ж587")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           | MPUIPC0    => stm_seq (stm_let "ж595"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUIPC0_reg_596"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUIPC0_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 0 8) (exp_var "жreg_MPUIPC0_reg_596") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUIPC0_reg (exp_var "ж595")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           | MPUIPSEGB1 => stm_seq (stm_let "ж599"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUIPSEGB1_reg_600"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUIPSEGB1_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 0 8) (exp_var "жreg_MPUIPSEGB1_reg_600") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUIPSEGB1_reg (exp_var "ж599")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           | MPUIPSEGB2 => stm_seq (stm_let "ж597"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUIPSEGB2_reg_598"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUIPSEGB2_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 0 8) (exp_var "жreg_MPUIPSEGB2_reg_598") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUIPSEGB2_reg (exp_var "ж597")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           | MPUSAM     => stm_seq (stm_let "ж593"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUSAM_reg_594"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUSAM_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 0 8) (exp_var "жreg_MPUSAM_reg_594") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUSAM_reg (exp_var "ж593")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           | MPUSEGB1   => stm_seq (stm_let "ж591"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUSEGB1_reg_592"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUSEGB1_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 0 8) (exp_var "жreg_MPUSEGB1_reg_592") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUSEGB1_reg (exp_var "ж591")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           | MPUSEGB2   => stm_seq (stm_let "ж589"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUSEGB2_reg_590"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUSEGB2_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 0 8) (exp_var "жreg_MPUSEGB2_reg_590") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUSEGB2_reg (exp_var "ж589")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           end)))
                                                                                                                                        (stm_let "ж610"
                                                                                                                                                 (ty.enum Empu_register_name)
                                                                                                                                                 (stm_exp (exp_var "reg"))
                                                                                                                                                 (stm_match_enum Empu_register_name
                                                                                                                                                                 (stm_exp (exp_var "ж610"))
                                                                                                                                                                 (fun K => match K with
                                                                                                                                                                           | MPUCTL0    => stm_seq (stm_let "ж611"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUCTL0_reg_612"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUCTL0_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 8 8) (exp_var "жreg_MPUCTL0_reg_612") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUCTL0_reg (exp_var "ж611")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           | MPUCTL1    => stm_seq (stm_let "ж613"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUCTL1_reg_614"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUCTL1_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 8 8) (exp_var "жreg_MPUCTL1_reg_614") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUCTL1_reg (exp_var "ж613")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           | MPUIPC0    => stm_seq (stm_let "ж621"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUIPC0_reg_622"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUIPC0_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 8 8) (exp_var "жreg_MPUIPC0_reg_622") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUIPC0_reg (exp_var "ж621")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           | MPUIPSEGB1 => stm_seq (stm_let "ж625"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUIPSEGB1_reg_626"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUIPSEGB1_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 8 8) (exp_var "жreg_MPUIPSEGB1_reg_626") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUIPSEGB1_reg (exp_var "ж625")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           | MPUIPSEGB2 => stm_seq (stm_let "ж623"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUIPSEGB2_reg_624"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUIPSEGB2_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 8 8) (exp_var "жreg_MPUIPSEGB2_reg_624") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUIPSEGB2_reg (exp_var "ж623")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           | MPUSAM     => stm_seq (stm_let "ж619"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUSAM_reg_620"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUSAM_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 8 8) (exp_var "жreg_MPUSAM_reg_620") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUSAM_reg (exp_var "ж619")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           | MPUSEGB1   => stm_seq (stm_let "ж617"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUSEGB1_reg_618"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUSEGB1_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 8 8) (exp_var "жreg_MPUSEGB1_reg_618") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUSEGB1_reg (exp_var "ж617")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           | MPUSEGB2   => stm_seq (stm_let "ж615"
                                                                                                                                                                                                            (ty.wordBits)
                                                                                                                                                                                                            (stm_let "жreg_MPUSEGB2_reg_616"
                                                                                                                                                                                                                     (ty.wordBits)
                                                                                                                                                                                                                     (stm_read_register MPUSEGB2_reg)
                                                                                                                                                                                                                     (stm_exp (exp_binop (bop.update_vector_subrange 8 8) (exp_var "жreg_MPUSEGB2_reg_616") (exp_var "v"))))
                                                                                                                                                                                                            (stm_write_register MPUSEGB2_reg (exp_var "ж615")))
                                                                                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt)))
                                                                                                                                                                           end)))))))))))))
                                                 (stm_assert (exp_false) (exp_string "../msp430-ipe-sail/_compilation/mpu.sail:105.19-105.20")))))).
    
    (*
      Extended type
        parameter _ж640
          unit
        return value
          ?[28]
      
      [0] : Sail type: {('ex12499# : Int), (0 <= 'ex12499# & 'ex12499# <= (2 ^ 16 - 1)). int(('ex12499# * 16))}
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 455
            Sail position: UnknownLocation
    *)
    Definition fun_ipe_lower : Stm [
                                     "_ж640"  ∷  ty.unit
                                   ]
                                   (ty.int) :=
      stm_let "ga#134"
              (ty.int)
              (stm_let "жreg_MPUIPSEGB1_reg_641"
                       (ty.wordBits)
                       (stm_read_register MPUIPSEGB1_reg)
                       (stm_exp (exp_unop uop.unsigned (exp_var "жreg_MPUIPSEGB1_reg_641"))))
              (stm_exp (((exp_var "ga#134"))*((exp_int 16%Z)))).
    
    (*
      Extended type
        parameter _ж642
          unit
        return value
          ?[29]
      
      [0] : Sail type: {('ex12502# : Int), (0 <= 'ex12502# & 'ex12502# <= (2 ^ 16 - 1)). int(('ex12502# * 16))}
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 455
            Sail position: UnknownLocation
    *)
    Definition fun_ipe_higher : Stm [
                                      "_ж642"  ∷  ty.unit
                                    ]
                                    (ty.int) :=
      stm_let "ga#135"
              (ty.int)
              (stm_let "жreg_MPUIPSEGB2_reg_643"
                       (ty.wordBits)
                       (stm_read_register MPUIPSEGB2_reg)
                       (stm_exp (exp_unop uop.unsigned (exp_var "жreg_MPUIPSEGB2_reg_643"))))
              (stm_exp (((exp_var "ga#135"))*((exp_int 16%Z)))).
    
    (*
      Extended type
        parameter addr
          ?[30:16]
        return value
          ?[31]
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
      
      [1] : Sail type: {('ex12527# : Bool) ('ex12517# : Int) ('ex12518# : Int), (0 <= 'ex12518# & 'ex12518# <= (2 ^ 16 - 1)). bool(('ex12527# & 'ex12517# <= 'ex12518#))}
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 455
            Sail position: UnknownLocation
    *)
    Definition fun_in_ipe_segment : Stm [
                                          "addr"  ∷  ty.bvec (16)
                                        ]
                                        (ty.bool) :=
      stm_let "ga#140"
              (ty.bool)
              (stm_let "ga#136"
                       (ty.int)
                       (stm_call ipe_lower (env.snoc (env.nil)
                                                     (_::_)
                                                     ((exp_val (ty.unit) (tt)))%exp))
                       (stm_let "ga#137"
                                (ty.int)
                                (stm_exp (exp_unop uop.unsigned (exp_var "addr")))
                                (stm_exp (((exp_var "ga#136"))<=((exp_var "ga#137"))))))
              (stm_let "ж644"
                       (ty.bool)
                       (stm_exp (exp_var "ga#140"))
                       (stm_if ((stm_exp (exp_var "ж644")))
                               (stm_let "ga#138"
                                        (ty.int)
                                        (stm_exp (exp_unop uop.unsigned (exp_var "addr")))
                                        (stm_let "ga#139"
                                                 (ty.int)
                                                 (stm_call ipe_higher (env.snoc (env.nil)
                                                                                (_::_)
                                                                                ((exp_val (ty.unit) (tt)))%exp))
                                                 (stm_exp (((exp_var "ga#138"))<((exp_var "ga#139"))))))
                               (stm_exp (exp_false)))).
    
    (*
      Extended type
        parameter addr
          ?[32:16]
        return value
          ?[33]
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
      
      [1] : Sail type: {('ex12557# : Bool) ('ex12547# : Int) ('ex12548# : Int), ((0 <= 'ex12548# & 'ex12548# <= (2 ^ 16 - 1)) & (0 <= 'ex12547# & 'ex12547# <= (2 ^ 16 - 1))). bool(('ex12557# & 'ex12547# <= 'ex12548#))}
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 455
            Sail position: UnknownLocation
    *)
    Definition fun_in_ivt_or_rv : Stm [
                                        "addr"  ∷  ty.bvec (16)
                                      ]
                                      (ty.bool) :=
      stm_let "ga#145"
              (ty.bool)
              (stm_let "ga#141"
                       (ty.int)
                       (stm_exp (exp_unop uop.unsigned (exp_val (ty.bvec 16) ([bv 65408]))))
                       (stm_let "ga#142"
                                (ty.int)
                                (stm_exp (exp_unop uop.unsigned (exp_var "addr")))
                                (stm_exp (((exp_var "ga#141"))<=((exp_var "ga#142"))))))
              (stm_let "ж645"
                       (ty.bool)
                       (stm_exp (exp_var "ga#145"))
                       (stm_if ((stm_exp (exp_var "ж645")))
                               (stm_let "ga#143"
                                        (ty.int)
                                        (stm_exp (exp_unop uop.unsigned (exp_var "addr")))
                                        (stm_let "ga#144"
                                                 (ty.int)
                                                 (stm_exp (exp_unop uop.unsigned (exp_val (ty.bvec 16) ([bv 65535]))))
                                                 (stm_exp (((exp_var "ga#143"))<=((exp_var "ga#144"))))))
                               (stm_exp (exp_false)))).
    
    (*
      Extended type
        parameter m
          access_mode
        return value
          $0
    *)
    Definition fun_is_x : Stm [
                                "m"  ∷  ty.enum Eaccess_mode
                              ]
                              (ty.bool) :=
      stm_let "ж646"
              (ty.enum Eaccess_mode)
              (stm_exp (exp_var "m"))
              (stm_match_enum Eaccess_mode
                              (stm_exp (exp_var "ж646"))
                              (fun K => match K with
                                        | R => stm_exp (exp_false)
                                        | W => stm_exp (exp_false)
                                        | X => stm_exp (exp_true)
                                        end)).
    
    (*
      Extended type
        parameter addr
          ?[34:16]
        parameter m
          access_mode
        return value
          $0
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_check_ipe_access : Stm [
                                            "addr"  ∷  ty.bvec (16);
                                            "m"  ∷  ty.enum Eaccess_mode
                                          ]
                                          (ty.bool) :=
      stm_let "pc"
              (ty.int)
              (stm_let "жreg_PC_reg_652"
                       (ty.wordBits)
                       (stm_read_register PC_reg)
                       (stm_exp (exp_unop uop.unsigned (exp_var "жreg_PC_reg_652"))))
              (stm_let "ga#156"
                       (ty.bool)
                       (stm_let "ga#146"
                                (ty.bvec (1))
                                (stm_let "жreg_MPUIPC0_reg_653"
                                         (ty.wordBits)
                                         (stm_read_register MPUIPC0_reg)
                                         (stm_exp (exp_unop (uop.vector_subrange 6 1) (exp_var "жreg_MPUIPC0_reg_653"))))
                                (stm_exp (((exp_var "ga#146") = (exp_val (ty.bvec 1) ([bv 0]))))))
                       (stm_let "ж658"
                                (ty.bool)
                                (stm_exp (exp_var "ga#156"))
                                (stm_if ((stm_exp (exp_var "ж658")))
                                        (stm_exp (exp_true))
                                        (stm_let "ga#155"
                                                 (ty.bool)
                                                 (stm_let "ga#147"
                                                          (ty.bool)
                                                          (stm_call in_ipe_segment (env.snoc (env.nil)
                                                                                             (_::_)
                                                                                             ((exp_var "addr"))%exp))
                                                          (stm_exp (exp_unop uop.not (exp_var "ga#147"))))
                                                 (stm_let "ж657"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#155"))
                                                          (stm_if ((stm_exp (exp_var "ж657")))
                                                                  (stm_exp (exp_true))
                                                                  (stm_let "ga#154"
                                                                           (ty.bool)
                                                                           (stm_let "ga#151"
                                                                                    (ty.bool)
                                                                                    (stm_let "ga#149"
                                                                                             (ty.int)
                                                                                             (stm_let "ga#148"
                                                                                                      (ty.int)
                                                                                                      (stm_call ipe_lower (env.snoc (env.nil)
                                                                                                                                    (_::_)
                                                                                                                                    ((exp_val (ty.unit) (tt)))%exp))
                                                                                                      (stm_exp (((exp_var "ga#148"))+((exp_int 8%Z)))))
                                                                                             (stm_exp (((exp_var "ga#149"))<=((exp_var "pc")))))
                                                                                    (stm_let "ж654"
                                                                                             (ty.bool)
                                                                                             (stm_exp (exp_var "ga#151"))
                                                                                             (stm_if ((stm_exp (exp_var "ж654")))
                                                                                                     (stm_let "ga#150"
                                                                                                              (ty.int)
                                                                                                              (stm_call ipe_higher (env.snoc (env.nil)
                                                                                                                                             (_::_)
                                                                                                                                             ((exp_val (ty.unit) (tt)))%exp))
                                                                                                              (stm_exp (((exp_var "pc"))<((exp_var "ga#150")))))
                                                                                                     (stm_exp (exp_false)))))
                                                                           (stm_let "ж656"
                                                                                    (ty.bool)
                                                                                    (stm_exp (exp_var "ga#154"))
                                                                                    (stm_if ((stm_exp (exp_var "ж656")))
                                                                                            (stm_let "ga#153"
                                                                                                     (ty.bool)
                                                                                                     (stm_let "ga#152"
                                                                                                              (ty.bool)
                                                                                                              (stm_call is_x (env.snoc (env.nil)
                                                                                                                                       (_::_)
                                                                                                                                       ((exp_var "m"))%exp))
                                                                                                              (stm_let "ж655"
                                                                                                                       (ty.bool)
                                                                                                                       (stm_exp (exp_var "ga#152"))
                                                                                                                       (stm_if ((stm_exp (exp_var "ж655")))
                                                                                                                               (stm_call in_ivt_or_rv (env.snoc (env.nil)
                                                                                                                                                                (_::_)
                                                                                                                                                                ((exp_var "addr"))%exp))
                                                                                                                               (stm_exp (exp_false)))))
                                                                                                     (stm_exp (exp_unop uop.not (exp_var "ga#153"))))
                                                                                            (stm_exp (exp_false))))))))))).
    
    (*
      Extended type
        parameter addr
          ?[35:16]
        parameter m
          access_mode
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_check_byte_access : Stm [
                                             "addr"  ∷  ty.bvec (16);
                                             "m"  ∷  ty.enum Eaccess_mode
                                           ]
                                           (ty.unit) :=
      stm_let "ga#158"
              (ty.bool)
              (stm_let "ga#157"
                       (ty.bool)
                       (stm_call check_ipe_access (env.snoc (env.snoc (env.nil)
                                                                      (_::_)
                                                                      ((exp_var "addr"))%exp)
                                                            (_::_)
                                                            ((exp_var "m"))%exp))
                       (stm_exp (exp_unop uop.not (exp_var "ga#157"))))
              (stm_let "ж659"
                       (ty.bool)
                       (stm_exp (exp_var "ga#158"))
                       (stm_if ((stm_exp (exp_var "ж659")))
                               (stm_seq (stm_exp (exp_union Uexception Kipe_violation (exp_var "addr")))
                                        (stm_fail _ "failure"))
                               (stm_exp (exp_val (ty.unit) (tt))))).
    
    (*
      Extended type
        parameter bw
          BW
        parameter addr
          ?[36:16]
        parameter m
          access_mode
        return value
          WordByte
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_read_mem_aux : Stm [
                                        "bw"  ∷  ty.enum Ebw;
                                        "addr"  ∷  ty.bvec (16);
                                        "m"  ∷  ty.enum Eaccess_mode
                                      ]
                                      (ty.union Uwordbyte) :=
      stm_let "ж660"
              (ty.enum Ebw)
              (stm_exp (exp_var "bw"))
              (stm_match_enum Ebw
                              (stm_exp (exp_var "ж660"))
                              (fun K => match K with
                                        | BYTE_INSTRUCTION => stm_seq (stm_call check_byte_access (env.snoc (env.snoc (env.nil)
                                                                                                                      (_::_)
                                                                                                                      ((exp_var "addr"))%exp)
                                                                                                            (_::_)
                                                                                                            ((exp_var "m"))%exp))
                                                                      (stm_let "ga#162"
                                                                               (ty.bvec (8))
                                                                               (stm_let "ga#161"
                                                                                        (ty.bool)
                                                                                        (stm_call is_mpu_reg_addr (env.snoc (env.nil)
                                                                                                                            (_::_)
                                                                                                                            ((exp_var "addr"))%exp))
                                                                                        (stm_let "ж662"
                                                                                                 (ty.bool)
                                                                                                 (stm_exp (exp_var "ga#161"))
                                                                                                 (stm_if ((stm_exp (exp_var "ж662")))
                                                                                                         (stm_call read_mpu_reg_byte (env.snoc (env.nil)
                                                                                                                                               (_::_)
                                                                                                                                               ((exp_var "addr"))%exp))
                                                                                                         (stm_call read_ram (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                    (_::_)
                                                                                                                                                                    ((exp_int 16%Z))%exp)
                                                                                                                                                          (_::_)
                                                                                                                                                          ((exp_int 1%Z))%exp)
                                                                                                                                                (_::_)
                                                                                                                                                ((exp_val (ty.bvec 16) ([bv 0])))%exp)
                                                                                                                                      (_::_)
                                                                                                                                      ((exp_var "addr"))%exp)))))
                                                                               (stm_exp (exp_union Uwordbyte Kbyte (exp_var "ga#162"))))
                                        | WORD_INSTRUCTION => stm_let "addr"
                                                                      (ty.bvec (16))
                                                                      (stm_exp (exp_binop bop.bvand (exp_var "addr") (exp_val (ty.bvec 16) ([bv 65534]))))
                                                                      (stm_let "ga#163"
                                                                               (ty.union Uwordbyte)
                                                                               (stm_call read_mem_aux (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                    (_::_)
                                                                                                                                    ((exp_val (ty.enum Ebw) (BYTE_INSTRUCTION)))%exp)
                                                                                                                          (_::_)
                                                                                                                          ((exp_var "addr"))%exp)
                                                                                                                (_::_)
                                                                                                                ((exp_var "m"))%exp))
                                                                               (stm_let "ж665"
                                                                                        (ty.union Uwordbyte)
                                                                                        (stm_exp (exp_var "ga#163"))
                                                                                        (stm_match_union_alt_list Uwordbyte
                                                                                                                  (stm_exp (exp_var "ж665"))
                                                                                                                  [
                                                                                                                    existT Kbyte (MkAlt (pat_var "l") (stm_let "ga#165"
                                                                                                                                                               (ty.union Uwordbyte)
                                                                                                                                                               (stm_let "ga#164"
                                                                                                                                                                        (ty.bvec (16))
                                                                                                                                                                        (stm_exp (exp_binop bop.bvadd (exp_var "addr") (exp_val (ty.bvec 16) ([bv 1]))))
                                                                                                                                                                        (stm_call read_mem_aux (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                                             (_::_)
                                                                                                                                                                                                                             ((exp_val (ty.enum Ebw) (BYTE_INSTRUCTION)))%exp)
                                                                                                                                                                                                                   (_::_)
                                                                                                                                                                                                                   ((exp_var "ga#164"))%exp)
                                                                                                                                                                                                         (_::_)
                                                                                                                                                                                                         ((exp_var "m"))%exp)))
                                                                                                                                                               (stm_let "ж666"
                                                                                                                                                                        (ty.union Uwordbyte)
                                                                                                                                                                        (stm_exp (exp_var "ga#165"))
                                                                                                                                                                        (stm_match_union_alt_list Uwordbyte
                                                                                                                                                                                                  (stm_exp (exp_var "ж666"))
                                                                                                                                                                                                  [
                                                                                                                                                                                                    existT Kbyte (MkAlt (pat_var "h") (stm_let "ga#166"
                                                                                                                                                                                                                                               (ty.bvec (16))
                                                                                                                                                                                                                                               (stm_exp (exp_binop (@bop.bvapp _ 8 8) (exp_var "h") (exp_var "l")))
                                                                                                                                                                                                                                               (stm_exp (exp_union Uwordbyte Kword (exp_var "ga#166")))));
                                                                                                                                                                                                    existT Kword (MkAlt (pat_var "ж672") (stm_fail _ "failure"))
                                                                                                                                                                                                  ]
                                                                                                                                                                                                  Logic.I))));
                                                                                                                    existT Kword (MkAlt (pat_var "ж678") (stm_fail _ "failure"))
                                                                                                                  ]
                                                                                                                  Logic.I)))
                                        end)).
    
    (*
      Extended type
        parameter bw
          BW
        parameter addr
          ?[37:16]
        return value
          WordByte
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_readMem : Stm [
                                   "bw"  ∷  ty.enum Ebw;
                                   "addr"  ∷  ty.bvec (16)
                                 ]
                                 (ty.union Uwordbyte) :=
      stm_call read_mem_aux (env.snoc (env.snoc (env.snoc (env.nil)
                                                          (_::_)
                                                          ((exp_var "bw"))%exp)
                                                (_::_)
                                                ((exp_var "addr"))%exp)
                                      (_::_)
                                      ((exp_val (ty.enum Eaccess_mode) (R)))%exp).
    
    (*
      Extended type
        parameter bw
          BW
        parameter addr
          ?[38:16]
        parameter v
          WordByte
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_writeMem : Stm [
                                    "bw"  ∷  ty.enum Ebw;
                                    "addr"  ∷  ty.bvec (16);
                                    "v"  ∷  ty.union Uwordbyte
                                  ]
                                  (ty.unit) :=
      stm_let "ж682"
              (ty.enum Ebw)
              (stm_exp (exp_var "bw"))
              (stm_match_enum Ebw
                              (stm_exp (exp_var "ж682"))
                              (fun K => match K with
                                        | BYTE_INSTRUCTION => stm_let "ж683"
                                                                      (ty.union Uwordbyte)
                                                                      (stm_exp (exp_var "v"))
                                                                      (stm_match_union_alt_list Uwordbyte
                                                                                                (stm_exp (exp_var "ж683"))
                                                                                                [
                                                                                                  existT Kbyte (MkAlt (pat_var "v") (stm_seq (stm_call check_byte_access (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                             (_::_)
                                                                                                                                                                                             ((exp_var "addr"))%exp)
                                                                                                                                                                                   (_::_)
                                                                                                                                                                                   ((exp_val (ty.enum Eaccess_mode) (W)))%exp))
                                                                                                                                             (stm_let "ga#168"
                                                                                                                                                      (ty.bool)
                                                                                                                                                      (stm_call is_mpu_reg_addr (env.snoc (env.nil)
                                                                                                                                                                                          (_::_)
                                                                                                                                                                                          ((exp_var "addr"))%exp))
                                                                                                                                                      (stm_let "ж685"
                                                                                                                                                               (ty.bool)
                                                                                                                                                               (stm_exp (exp_var "ga#168"))
                                                                                                                                                               (stm_if ((stm_exp (exp_var "ж685")))
                                                                                                                                                                       (stm_call write_mpu_reg_byte (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                                        (_::_)
                                                                                                                                                                                                                        ((exp_var "addr"))%exp)
                                                                                                                                                                                                              (_::_)
                                                                                                                                                                                                              ((exp_var "v"))%exp))
                                                                                                                                                                       (stm_call write_ram (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                                                             (_::_)
                                                                                                                                                                                                                                             ((exp_int 16%Z))%exp)
                                                                                                                                                                                                                                   (_::_)
                                                                                                                                                                                                                                   ((exp_int 1%Z))%exp)
                                                                                                                                                                                                                         (_::_)
                                                                                                                                                                                                                         ((exp_val (ty.bvec 16) ([bv 0])))%exp)
                                                                                                                                                                                                               (_::_)
                                                                                                                                                                                                               ((exp_var "addr"))%exp)
                                                                                                                                                                                                     (_::_)
                                                                                                                                                                                                     ((exp_var "v"))%exp)))))));
                                                                                                  existT Kword (MkAlt (pat_var "v") (stm_let "ga#170"
                                                                                                                                             ((ty.union Uwordbyte))
                                                                                                                                             (stm_let "ga#169"
                                                                                                                                                      (ty.bvec (8))
                                                                                                                                                      (stm_exp (exp_unop (uop.vector_subrange 0 8) (exp_var "v")))
                                                                                                                                                      (stm_exp (exp_union Uwordbyte Kbyte (exp_var "ga#169"))))
                                                                                                                                             (stm_call writeMem (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                              (_::_)
                                                                                                                                                                                              ((exp_val (ty.enum Ebw) (BYTE_INSTRUCTION)))%exp)
                                                                                                                                                                                    (_::_)
                                                                                                                                                                                    ((exp_var "addr"))%exp)
                                                                                                                                                                          (_::_)
                                                                                                                                                                          ((exp_var "ga#170"))%exp))))
                                                                                                ]
                                                                                                Logic.I)
                                        | WORD_INSTRUCTION => stm_let "ж693"
                                                                      (ty.union Uwordbyte)
                                                                      (stm_exp (exp_var "v"))
                                                                      (stm_match_union_alt_list Uwordbyte
                                                                                                (stm_exp (exp_var "ж693"))
                                                                                                [
                                                                                                  existT Kbyte (MkAlt (pat_var "v") (stm_let "ga#178"
                                                                                                                                             ((ty.union Uwordbyte))
                                                                                                                                             (stm_let "ga#177"
                                                                                                                                                      (ty.bvec (16))
                                                                                                                                                      (stm_exp (exp_unop (uop.zext (n := 16)) (exp_var "v")))
                                                                                                                                                      (stm_exp (exp_union Uwordbyte Kword (exp_var "ga#177"))))
                                                                                                                                             (stm_call writeMem (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                              (_::_)
                                                                                                                                                                                              ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                                                                                                                                                    (_::_)
                                                                                                                                                                                    ((exp_var "addr"))%exp)
                                                                                                                                                                          (_::_)
                                                                                                                                                                          ((exp_var "ga#178"))%exp))));
                                                                                                  existT Kword (MkAlt (pat_var "v") (stm_seq (stm_let "addr"
                                                                                                                                                      (ty.bvec (16))
                                                                                                                                                      (stm_exp (exp_binop bop.bvand (exp_var "addr") (exp_val (ty.bvec 16) ([bv 65534]))))
                                                                                                                                                      (stm_let "ga#172"
                                                                                                                                                               ((ty.union Uwordbyte))
                                                                                                                                                               (stm_let "ga#171"
                                                                                                                                                                        (ty.bvec (8))
                                                                                                                                                                        (stm_exp (exp_unop (uop.vector_subrange 0 8) (exp_var "v")))
                                                                                                                                                                        (stm_exp (exp_union Uwordbyte Kbyte (exp_var "ga#171"))))
                                                                                                                                                               (stm_call writeMem (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                                (_::_)
                                                                                                                                                                                                                ((exp_val (ty.enum Ebw) (BYTE_INSTRUCTION)))%exp)
                                                                                                                                                                                                      (_::_)
                                                                                                                                                                                                      ((exp_var "addr"))%exp)
                                                                                                                                                                                            (_::_)
                                                                                                                                                                                            ((exp_var "ga#172"))%exp))))
                                                                                                                                             (stm_let "ga#175"
                                                                                                                                                      (ty.bvec (16))
                                                                                                                                                      (stm_exp (exp_binop bop.bvadd (exp_var "addr") (exp_val (ty.bvec 16) ([bv 1]))))
                                                                                                                                                      (stm_let "ga#176"
                                                                                                                                                               ((ty.union Uwordbyte))
                                                                                                                                                               (stm_let "ga#174"
                                                                                                                                                                        (ty.bvec (8))
                                                                                                                                                                        (stm_exp (exp_unop (uop.vector_subrange 8 8) (exp_var "v")))
                                                                                                                                                                        (stm_exp (exp_union Uwordbyte Kbyte (exp_var "ga#174"))))
                                                                                                                                                               (stm_call writeMem (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                                (_::_)
                                                                                                                                                                                                                ((exp_val (ty.enum Ebw) (BYTE_INSTRUCTION)))%exp)
                                                                                                                                                                                                      (_::_)
                                                                                                                                                                                                      ((exp_var "ga#175"))%exp)
                                                                                                                                                                                            (_::_)
                                                                                                                                                                                            ((exp_var "ga#176"))%exp))))))
                                                                                                ]
                                                                                                Logic.I)
                                        end)).
    
    (*
      Extended type
        parameter bw
          BW
        parameter address
          ?[39:16]
        return value
          WordByte
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_readMemInstruction : Stm [
                                              "bw"  ∷  ty.enum Ebw;
                                              "address"  ∷  ty.bvec (16)
                                            ]
                                            (ty.union Uwordbyte) :=
      stm_let "res"
              (ty.union Uwordbyte)
              (stm_call readMem (env.snoc (env.snoc (env.nil)
                                                    (_::_)
                                                    ((exp_var "bw"))%exp)
                                          (_::_)
                                          ((exp_var "address"))%exp))
              (stm_seq (stm_let "ga#189"
                                (ty.string)
                                (stm_let "ga#187"
                                         (ty.string)
                                         (stm_let "ga#186"
                                                  (ty.string)
                                                  (stm_let "ga#184"
                                                           (ty.string)
                                                           (stm_let "ga#183"
                                                                    (ty.string)
                                                                    (stm_let "ga#181"
                                                                             (ty.string)
                                                                             (stm_let "ga#180"
                                                                                      (ty.string)
                                                                                      (stm_let "ga#179"
                                                                                               (ty.string)
                                                                                               (stm_let "жreg_old_PC_reg_705"
                                                                                                        (ty.wordBits)
                                                                                                        (stm_read_register old_PC_reg)
                                                                                                        (stm_call bits_str (env.snoc (env.nil)
                                                                                                                                     (_::_)
                                                                                                                                     ((exp_var "жreg_old_PC_reg_705"))%exp)))
                                                                                               (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                        (_::_)
                                                                                                                                        ((exp_string "memory:"))%exp)
                                                                                                                              (_::_)
                                                                                                                              ((exp_var "ga#179"))%exp)))
                                                                                      (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                               (_::_)
                                                                                                                               ((exp_var "ga#180"))%exp)
                                                                                                                     (_::_)
                                                                                                                     ((exp_string "   -GET: ["))%exp)))
                                                                             (stm_let "ga#182"
                                                                                      (ty.string)
                                                                                      (stm_call bits_str (env.snoc (env.nil)
                                                                                                                   (_::_)
                                                                                                                   ((exp_var "address"))%exp))
                                                                                      (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                               (_::_)
                                                                                                                               ((exp_var "ga#181"))%exp)
                                                                                                                     (_::_)
                                                                                                                     ((exp_var "ga#182"))%exp))))
                                                                    (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                             (_::_)
                                                                                                             ((exp_var "ga#183"))%exp)
                                                                                                   (_::_)
                                                                                                   ((exp_string "]"))%exp)))
                                                           (stm_let "ga#185"
                                                                    (ty.string)
                                                                    (stm_call BWSizeString (env.snoc (env.nil)
                                                                                                     (_::_)
                                                                                                     ((exp_var "bw"))%exp))
                                                                    (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                             (_::_)
                                                                                                             ((exp_var "ga#184"))%exp)
                                                                                                   (_::_)
                                                                                                   ((exp_var "ga#185"))%exp))))
                                                  (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                           (_::_)
                                                                                           ((exp_var "ga#186"))%exp)
                                                                                 (_::_)
                                                                                 ((exp_string "->"))%exp)))
                                         (stm_let "ga#188"
                                                  (ty.string)
                                                  (stm_call WordByteString (env.snoc (env.nil)
                                                                                     (_::_)
                                                                                     ((exp_var "res"))%exp))
                                                  (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                           (_::_)
                                                                                           ((exp_var "ga#187"))%exp)
                                                                                 (_::_)
                                                                                 ((exp_var "ga#188"))%exp))))
                                (stm_call logWithVerbosity (env.snoc (env.snoc (env.nil)
                                                                               (_::_)
                                                                               ((exp_int 4%Z))%exp)
                                                                     (_::_)
                                                                     ((exp_var "ga#189"))%exp)))
                       (stm_exp (exp_var "res"))).
    
    (*
      Extended type
        parameter bw
          BW
        parameter address
          ?[40:16]
        parameter value
          WordByte
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_writeMemInstruction : Stm [
                                               "bw"  ∷  ty.enum Ebw;
                                               "address"  ∷  ty.bvec (16);
                                               "value"  ∷  ty.union Uwordbyte
                                             ]
                                             (ty.unit) :=
      stm_seq (stm_let "ga#201"
                       (ty.string)
                       (stm_let "ga#199"
                                (ty.string)
                                (stm_let "ga#198"
                                         (ty.string)
                                         (stm_let "ga#196"
                                                  (ty.string)
                                                  (stm_let "ga#195"
                                                           (ty.string)
                                                           (stm_let "ga#193"
                                                                    (ty.string)
                                                                    (stm_let "ga#192"
                                                                             (ty.string)
                                                                             (stm_let "ga#191"
                                                                                      (ty.string)
                                                                                      (stm_let "жreg_old_PC_reg_709"
                                                                                               (ty.wordBits)
                                                                                               (stm_read_register old_PC_reg)
                                                                                               (stm_call bits_str (env.snoc (env.nil)
                                                                                                                            (_::_)
                                                                                                                            ((exp_var "жreg_old_PC_reg_709"))%exp)))
                                                                                      (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                               (_::_)
                                                                                                                               ((exp_string "memory:"))%exp)
                                                                                                                     (_::_)
                                                                                                                     ((exp_var "ga#191"))%exp)))
                                                                             (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                      (_::_)
                                                                                                                      ((exp_var "ga#192"))%exp)
                                                                                                            (_::_)
                                                                                                            ((exp_string "   -PUT: ["))%exp)))
                                                                    (stm_let "ga#194"
                                                                             (ty.string)
                                                                             (stm_call bits_str (env.snoc (env.nil)
                                                                                                          (_::_)
                                                                                                          ((exp_var "address"))%exp))
                                                                             (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                      (_::_)
                                                                                                                      ((exp_var "ga#193"))%exp)
                                                                                                            (_::_)
                                                                                                            ((exp_var "ga#194"))%exp))))
                                                           (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                    (_::_)
                                                                                                    ((exp_var "ga#195"))%exp)
                                                                                          (_::_)
                                                                                          ((exp_string "]"))%exp)))
                                                  (stm_let "ga#197"
                                                           (ty.string)
                                                           (stm_call BWSizeString (env.snoc (env.nil)
                                                                                            (_::_)
                                                                                            ((exp_var "bw"))%exp))
                                                           (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                    (_::_)
                                                                                                    ((exp_var "ga#196"))%exp)
                                                                                          (_::_)
                                                                                          ((exp_var "ga#197"))%exp))))
                                         (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                  (_::_)
                                                                                  ((exp_var "ga#198"))%exp)
                                                                        (_::_)
                                                                        ((exp_string "<-"))%exp)))
                                (stm_let "ga#200"
                                         (ty.string)
                                         (stm_call WordByteString (env.snoc (env.nil)
                                                                            (_::_)
                                                                            ((exp_var "value"))%exp))
                                         (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                  (_::_)
                                                                                  ((exp_var "ga#199"))%exp)
                                                                        (_::_)
                                                                        ((exp_var "ga#200"))%exp))))
                       (stm_call logWithVerbosity (env.snoc (env.snoc (env.nil)
                                                                      (_::_)
                                                                      ((exp_int 4%Z))%exp)
                                                            (_::_)
                                                            ((exp_var "ga#201"))%exp)))
              (stm_call writeMem (env.snoc (env.snoc (env.snoc (env.nil)
                                                               (_::_)
                                                               ((exp_var "bw"))%exp)
                                                     (_::_)
                                                     ((exp_var "address"))%exp)
                                           (_::_)
                                           ((exp_var "value"))%exp)).
    
    (*
      Extended type
        parameter _ж713
          unit
        return value
          unit
    *)
    Definition fun_incPC : Stm [
                                 "_ж713"  ∷  ty.unit
                               ]
                               (ty.unit) :=
      stm_seq (stm_let "ж714"
                       (ty.wordBits)
                       (stm_let "жreg_PC_reg_715"
                                (ty.wordBits)
                                (stm_read_register PC_reg)
                                (stm_exp (exp_binop bop.bvadd (exp_var "жreg_PC_reg_715") (exp_val (ty.bvec 16) ([bv 2])))))
                       (stm_write_register PC_reg (exp_var "ж714")))
              (stm_exp (exp_val (ty.unit) (tt))).
    
    (*
      Extended type
        parameter _ж716
          unit
        return value
          WordByte
    *)
    Definition fun_fetch : Stm [
                                 "_ж716"  ∷  ty.unit
                               ]
                               (ty.union Uwordbyte) :=
      stm_seq (stm_let "ga#205"
                       (ty.bool)
                       (stm_let "ga#204"
                                (ty.int)
                                (stm_let "ga#203"
                                         (ty.int)
                                         (stm_let "жreg_PC_reg_717"
                                                  (ty.wordBits)
                                                  (stm_read_register PC_reg)
                                                  (stm_exp (exp_unop uop.unsigned (exp_var "жreg_PC_reg_717"))))
                                         (stm_call emod_int (env.snoc (env.snoc (env.nil)
                                                                                (_::_)
                                                                                ((exp_var "ga#203"))%exp)
                                                                      (_::_)
                                                                      ((exp_int 2%Z))%exp)))
                                (stm_exp (((exp_var "ga#204"))=((exp_int 0%Z)))))
                       (stm_assert (exp_var "ga#205") (exp_string "PC is not correctly aligned")))
              (stm_let "data"
                       (ty.union Uwordbyte)
                       (stm_let "жreg_PC_reg_719"
                                (ty.wordBits)
                                (stm_read_register PC_reg)
                                (stm_call read_mem_aux (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                     (_::_)
                                                                                     ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                                           (_::_)
                                                                           ((exp_var "жreg_PC_reg_719"))%exp)
                                                                 (_::_)
                                                                 ((exp_val (ty.enum Eaccess_mode) (X)))%exp)))
                       (stm_seq (stm_call incPC (env.snoc (env.nil)
                                                          (_::_)
                                                          ((exp_val (ty.unit) (tt)))%exp))
                                (stm_exp (exp_var "data")))).
    
    (*
      Extended type
        parameter arg#
          AM
        return value
          ?[41]
      
      [0] : Sail type: bitvector(2)
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_sourcemaping_forwards : Stm [
                                                 "arg#"  ∷  ty.enum Eam
                                               ]
                                               (ty.bvec (2)) :=
      stm_let "ж725"
              (ty.enum Eam)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Eam
                              (stm_exp (exp_var "ж725"))
                              (fun K => match K with
                                        | INDEXED_MODE                => stm_exp (exp_val (ty.bvec 2) ([bv 1]))
                                        | INDIRECT_AUTOINCREMENT_MODE => stm_exp (exp_val (ty.bvec 2) ([bv 3]))
                                        | INDIRECT_REGISTER_MODE      => stm_exp (exp_val (ty.bvec 2) ([bv 2]))
                                        | REGISTER_MODE               => stm_exp (exp_val (ty.bvec 2) ([bv 0]))
                                        end)).
    
    (*
      Extended type
        parameter arg#
          ?[42:2]
        return value
          AM
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_sourcemaping_backwards : Stm [
                                                  "arg#"  ∷  ty.bvec (2)
                                                ]
                                                (ty.enum Eam) :=
      stm_let "b__0"
              (ty.bvec (2))
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#208"
                       (ty.bool)
                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 2) ([bv 0])))))
                       (stm_let "ж733"
                                (ty.bool)
                                (stm_exp (exp_var "ga#208"))
                                (stm_if ((stm_exp (exp_var "ж733")))
                                        (stm_exp (exp_val (ty.enum Eam) (REGISTER_MODE)))
                                        (stm_let "ga#209"
                                                 (ty.bool)
                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 2) ([bv 1])))))
                                                 (stm_let "ж732"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#209"))
                                                          (stm_if ((stm_exp (exp_var "ж732")))
                                                                  (stm_exp (exp_val (ty.enum Eam) (INDEXED_MODE)))
                                                                  (stm_let "ga#210"
                                                                           (ty.bool)
                                                                           (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 2) ([bv 2])))))
                                                                           (stm_let "ж731"
                                                                                    (ty.bool)
                                                                                    (stm_exp (exp_var "ga#210"))
                                                                                    (stm_if ((stm_exp (exp_var "ж731")))
                                                                                            (stm_exp (exp_val (ty.enum Eam) (INDIRECT_REGISTER_MODE)))
                                                                                            (stm_exp (exp_val (ty.enum Eam) (INDIRECT_AUTOINCREMENT_MODE)))))))))))).
    
    (*
      Extended type
        parameter arg#
          AM
        return value
          $0
    *)
    Definition fun_sourcemaping_forwards_matches : Stm [
                                                         "arg#"  ∷  ty.enum Eam
                                                       ]
                                                       (ty.bool) :=
      stm_let "ж734"
              (ty.enum Eam)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Eam
                              (stm_exp (exp_var "ж734"))
                              (fun K => match K with
                                        | INDEXED_MODE                => stm_exp (exp_true)
                                        | INDIRECT_AUTOINCREMENT_MODE => stm_exp (exp_true)
                                        | INDIRECT_REGISTER_MODE      => stm_exp (exp_true)
                                        | REGISTER_MODE               => stm_exp (exp_true)
                                        end)).
    
    (*
      Extended type
        parameter arg#
          ?[43:2]
        return value
          $0
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_sourcemaping_backwards_matches : Stm [
                                                          "arg#"  ∷  ty.bvec (2)
                                                        ]
                                                        (ty.bool) :=
      stm_let "b__0"
              (ty.bvec (2))
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#211"
                       (ty.bool)
                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 2) ([bv 0])))))
                       (stm_let "ж743"
                                (ty.bool)
                                (stm_exp (exp_var "ga#211"))
                                (stm_if ((stm_exp (exp_var "ж743")))
                                        (stm_exp (exp_true))
                                        (stm_let "ga#212"
                                                 (ty.bool)
                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 2) ([bv 1])))))
                                                 (stm_let "ж742"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#212"))
                                                          (stm_if ((stm_exp (exp_var "ж742")))
                                                                  (stm_exp (exp_true))
                                                                  (stm_let "ga#213"
                                                                           (ty.bool)
                                                                           (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 2) ([bv 2])))))
                                                                           (stm_let "ж741"
                                                                                    (ty.bool)
                                                                                    (stm_exp (exp_var "ga#213"))
                                                                                    (stm_if ((stm_exp (exp_var "ж741")))
                                                                                            (stm_exp (exp_true))
                                                                                            (stm_let "ga#214"
                                                                                                     (ty.bool)
                                                                                                     (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 2) ([bv 3])))))
                                                                                                     (stm_let "ж740"
                                                                                                              (ty.bool)
                                                                                                              (stm_exp (exp_var "ga#214"))
                                                                                                              (stm_if ((stm_exp (exp_var "ж740")))
                                                                                                                      (stm_exp (exp_true))
                                                                                                                      (stm_exp (exp_false)))))))))))))).
    
    (*
      Extended type
        parameter arg#
          AM
        return value
          ?[44]
      
      [0] : Sail type: bitvector(1)
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_destinationmaping_forwards : Stm [
                                                      "arg#"  ∷  ty.enum Eam
                                                    ]
                                                    (ty.bvec (1)) :=
      stm_let "ж744"
              (ty.enum Eam)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Eam
                              (stm_exp (exp_var "ж744"))
                              (fun K => match K with
                                        | INDEXED_MODE                => stm_exp (exp_val (ty.bvec 1) ([bv 1]))
                                        | INDIRECT_AUTOINCREMENT_MODE => stm_seq (stm_assert (exp_false) (exp_string "Pattern match failure at unknown location"))
                                                                                 (stm_fail _ "failure")
                                        | INDIRECT_REGISTER_MODE      => stm_seq (stm_assert (exp_false) (exp_string "Pattern match failure at unknown location"))
                                                                                 (stm_fail _ "failure")
                                        | REGISTER_MODE               => stm_exp (exp_val (ty.bvec 1) ([bv 0]))
                                        end)).
    
    (*
      Extended type
        parameter arg#
          ?[45:1]
        return value
          AM
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_destinationmaping_backwards : Stm [
                                                       "arg#"  ∷  ty.bvec (1)
                                                     ]
                                                     (ty.enum Eam) :=
      stm_let "b__0"
              (ty.bvec (1))
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#216"
                       (ty.bool)
                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 1) ([bv 0])))))
                       (stm_let "ж754"
                                (ty.bool)
                                (stm_exp (exp_var "ga#216"))
                                (stm_if ((stm_exp (exp_var "ж754")))
                                        (stm_exp (exp_val (ty.enum Eam) (REGISTER_MODE)))
                                        (stm_exp (exp_val (ty.enum Eam) (INDEXED_MODE)))))).
    
    (*
      Extended type
        parameter arg#
          AM
        return value
          $0
    *)
    Definition fun_destinationmaping_forwards_matches : Stm [
                                                              "arg#"  ∷  ty.enum Eam
                                                            ]
                                                            (ty.bool) :=
      stm_let "ж755"
              (ty.enum Eam)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Eam
                              (stm_exp (exp_var "ж755"))
                              (fun K => match K with
                                        | INDEXED_MODE                => stm_exp (exp_true)
                                        | INDIRECT_AUTOINCREMENT_MODE => stm_exp (exp_false)
                                        | INDIRECT_REGISTER_MODE      => stm_exp (exp_false)
                                        | REGISTER_MODE               => stm_exp (exp_true)
                                        end)).
    
    (*
      Extended type
        parameter arg#
          ?[46:1]
        return value
          $0
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_destinationmaping_backwards_matches : Stm [
                                                               "arg#"  ∷  ty.bvec (1)
                                                             ]
                                                             (ty.bool) :=
      stm_let "b__0"
              (ty.bvec (1))
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#217"
                       (ty.bool)
                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 1) ([bv 0])))))
                       (stm_let "ж763"
                                (ty.bool)
                                (stm_exp (exp_var "ga#217"))
                                (stm_if ((stm_exp (exp_var "ж763")))
                                        (stm_exp (exp_true))
                                        (stm_let "ga#218"
                                                 (ty.bool)
                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 1) ([bv 1])))))
                                                 (stm_let "ж762"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#218"))
                                                          (stm_if ((stm_exp (exp_var "ж762")))
                                                                  (stm_exp (exp_true))
                                                                  (stm_exp (exp_false)))))))).
    
    (*
      Extended type
        parameter bw
          BW
        parameter reg
          Register
        return value
          WordByte
    *)
    Definition fun_readReg : Stm [
                                   "bw"  ∷  ty.enum Ebw;
                                   "reg"  ∷  ty.enum Eregister
                                 ]
                                 (ty.union Uwordbyte) :=
      stm_let "ж764"
              (ty.enum Ebw)
              (stm_exp (exp_var "bw"))
              (stm_match_enum Ebw
                              (stm_exp (exp_var "ж764"))
                              (fun K => match K with
                                        | BYTE_INSTRUCTION => stm_let "ga#220"
                                                                      (ty.union Uwordbyte)
                                                                      (stm_call readReg (env.snoc (env.snoc (env.nil)
                                                                                                            (_::_)
                                                                                                            ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                                                                  (_::_)
                                                                                                  ((exp_var "reg"))%exp))
                                                                      (stm_let "ж799"
                                                                               (ty.union Uwordbyte)
                                                                               (stm_exp (exp_var "ga#220"))
                                                                               (stm_match_union_alt_list Uwordbyte
                                                                                                         (stm_exp (exp_var "ж799"))
                                                                                                         [
                                                                                                           existT Kbyte (MkAlt (pat_var "ж803") (stm_fail _ "failure"));
                                                                                                           existT Kword (MkAlt (pat_var "value") (stm_let "ga#221"
                                                                                                                                                          (ty.bvec (8))
                                                                                                                                                          (stm_exp (exp_unop (uop.vector_subrange 0 8) (exp_var "value")))
                                                                                                                                                          (stm_exp (exp_union Uwordbyte Kbyte (exp_var "ga#221")))))
                                                                                                         ]
                                                                                                         Logic.I))
                                        | WORD_INSTRUCTION => stm_let "ga#219"
                                                                      (ty.bvec (16))
                                                                      (stm_let "ж765"
                                                                               (ty.enum Eregister)
                                                                               (stm_exp (exp_var "reg"))
                                                                               (stm_match_enum Eregister
                                                                                               (stm_exp (exp_var "ж765"))
                                                                                               (fun K => match K with
                                                                                                         | CG2   => stm_let "жreg_CG2_reg_769"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register CG2_reg)
                                                                                                                            (stm_exp (exp_var "жreg_CG2_reg_769"))
                                                                                                         | PC    => stm_let "жreg_PC_reg_766"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register PC_reg)
                                                                                                                            (stm_exp (exp_var "жreg_PC_reg_766"))
                                                                                                         | R10   => stm_let "жreg_R10_reg_776"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register R10_reg)
                                                                                                                            (stm_exp (exp_var "жreg_R10_reg_776"))
                                                                                                         | R11   => stm_let "жreg_R11_reg_777"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register R11_reg)
                                                                                                                            (stm_exp (exp_var "жreg_R11_reg_777"))
                                                                                                         | R12   => stm_let "жreg_R12_reg_778"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register R12_reg)
                                                                                                                            (stm_exp (exp_var "жreg_R12_reg_778"))
                                                                                                         | R13   => stm_let "жreg_R13_reg_779"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register R13_reg)
                                                                                                                            (stm_exp (exp_var "жreg_R13_reg_779"))
                                                                                                         | R14   => stm_let "жreg_R14_reg_780"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register R14_reg)
                                                                                                                            (stm_exp (exp_var "жreg_R14_reg_780"))
                                                                                                         | R15   => stm_let "жreg_R15_reg_781"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register R15_reg)
                                                                                                                            (stm_exp (exp_var "жreg_R15_reg_781"))
                                                                                                         | R4    => stm_let "жreg_R4_reg_770"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register R4_reg)
                                                                                                                            (stm_exp (exp_var "жreg_R4_reg_770"))
                                                                                                         | R5    => stm_let "жreg_R5_reg_771"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register R5_reg)
                                                                                                                            (stm_exp (exp_var "жreg_R5_reg_771"))
                                                                                                         | R6    => stm_let "жreg_R6_reg_772"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register R6_reg)
                                                                                                                            (stm_exp (exp_var "жreg_R6_reg_772"))
                                                                                                         | R7    => stm_let "жreg_R7_reg_773"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register R7_reg)
                                                                                                                            (stm_exp (exp_var "жreg_R7_reg_773"))
                                                                                                         | R8    => stm_let "жreg_R8_reg_774"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register R8_reg)
                                                                                                                            (stm_exp (exp_var "жreg_R8_reg_774"))
                                                                                                         | R9    => stm_let "жreg_R9_reg_775"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register R9_reg)
                                                                                                                            (stm_exp (exp_var "жreg_R9_reg_775"))
                                                                                                         | SP    => stm_let "жreg_SP_reg_767"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register SP_reg)
                                                                                                                            (stm_exp (exp_var "жreg_SP_reg_767"))
                                                                                                         | SRCG1 => stm_let "жreg_SRCG1_reg_768"
                                                                                                                            (ty.wordBits)
                                                                                                                            (stm_read_register SRCG1_reg)
                                                                                                                            (stm_exp (exp_var "жreg_SRCG1_reg_768"))
                                                                                                         end)))
                                                                      (stm_exp (exp_union Uwordbyte Kword (exp_var "ga#219")))
                                        end)).
    
    (*
      Extended type
        parameter bw
          BW
        parameter reg
          Register
        parameter v
          WordByte
        return value
          unit
    *)
    Definition fun_writeReg : Stm [
                                    "bw"  ∷  ty.enum Ebw;
                                    "reg"  ∷  ty.enum Eregister;
                                    "v"  ∷  ty.union Uwordbyte
                                  ]
                                  (ty.unit) :=
      stm_let "v"
              (ty.wordBits)
              (stm_let "ж809"
                       (ty.union Uwordbyte)
                       (stm_exp (exp_var "v"))
                       (stm_match_union_alt_list Uwordbyte
                                                 (stm_exp (exp_var "ж809"))
                                                 [
                                                   existT Kbyte (MkAlt (pat_var "v") (stm_exp (exp_unop (uop.zext (n := 16)) (exp_var "v"))));
                                                   existT Kword (MkAlt (pat_var "v") (stm_exp (exp_var "v")))
                                                 ]
                                                 Logic.I))
              (stm_let "v"
                       (ty.wordBits)
                       (stm_let "ж815"
                                (ty.enum Ebw)
                                (stm_exp (exp_var "bw"))
                                (stm_match_enum Ebw
                                                (stm_exp (exp_var "ж815"))
                                                (fun K => match K with
                                                          | BYTE_INSTRUCTION => stm_let "ga#222"
                                                                                        (ty.bvec (8))
                                                                                        (stm_exp (exp_unop (uop.vector_subrange 0 8) (exp_var "v")))
                                                                                        (stm_exp (exp_unop (uop.zext (n := 16)) (exp_var "ga#222")))
                                                          | WORD_INSTRUCTION => stm_exp (exp_var "v")
                                                          end)))
                       (stm_let "ж819"
                                (ty.enum Eregister)
                                (stm_exp (exp_var "reg"))
                                (stm_match_enum Eregister
                                                (stm_exp (exp_var "ж819"))
                                                (fun K => match K with
                                                          | CG2   => stm_seq (stm_let "ж823"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register CG2_reg (exp_var "ж823")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | PC    => stm_seq (stm_let "ж820"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register PC_reg (exp_var "ж820")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | R10   => stm_seq (stm_let "ж830"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register R10_reg (exp_var "ж830")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | R11   => stm_seq (stm_let "ж831"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register R11_reg (exp_var "ж831")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | R12   => stm_seq (stm_let "ж832"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register R12_reg (exp_var "ж832")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | R13   => stm_seq (stm_let "ж833"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register R13_reg (exp_var "ж833")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | R14   => stm_seq (stm_let "ж834"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register R14_reg (exp_var "ж834")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | R15   => stm_seq (stm_let "ж835"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register R15_reg (exp_var "ж835")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | R4    => stm_seq (stm_let "ж824"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register R4_reg (exp_var "ж824")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | R5    => stm_seq (stm_let "ж825"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register R5_reg (exp_var "ж825")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | R6    => stm_seq (stm_let "ж826"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register R6_reg (exp_var "ж826")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | R7    => stm_seq (stm_let "ж827"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register R7_reg (exp_var "ж827")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | R8    => stm_seq (stm_let "ж828"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register R8_reg (exp_var "ж828")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | R9    => stm_seq (stm_let "ж829"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register R9_reg (exp_var "ж829")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | SP    => stm_seq (stm_let "ж821"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register SP_reg (exp_var "ж821")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          | SRCG1 => stm_seq (stm_let "ж822"
                                                                                      (ty.wordBits)
                                                                                      (stm_exp (exp_var "v"))
                                                                                      (stm_write_register SRCG1_reg (exp_var "ж822")))
                                                                             (stm_exp (exp_val (ty.unit) (tt)))
                                                          end)))).

    (*
      Extended type
        parameter bw
          BW
        parameter reg
          Register
        parameter am
          AM
        return value
          WordByte
    *)
    Definition fun_read : Stm [
                                "bw"  ∷  ty.enum Ebw;
                                "reg"  ∷  ty.enum Eregister;
                                "am"  ∷  ty.enum Eam
                              ]
                              (ty.union Uwordbyte) :=
      stm_let "ж853"
              (ty.tuple [
                          ty.enum Ebw;
                          ty.enum Eregister;
                          ty.enum Eam
                        ])
              (stm_exp (exp_tuple [ exp_var "bw"; exp_var "reg"; exp_var "am" ]))
              (stm_fail _ "").

    (*
      Extended type
        parameter bw
          BW
        parameter reg
          Register
        parameter am
          AM
        parameter v
          WordByte
        return value
          unit
    *)
    Definition fun_write : Stm [
                                 "bw"  ∷  ty.enum Ebw;
                                 "reg"  ∷  ty.enum Eregister;
                                 "am"  ∷  ty.enum Eam;
                                 "v"  ∷  ty.union Uwordbyte
                               ]
                               (ty.unit) :=
      stm_let "ж1423"
              (ty.tuple [
                          ty.enum Ebw;
                          ty.enum Eregister;
                          ty.enum Eam;
                          ty.union Uwordbyte
                        ])
              (stm_exp (exp_tuple [ exp_var "bw"; exp_var "reg"; exp_var "am";  exp_var "v" ]))
              (stm_fail _ "").

    (*
      Extended type
        parameter bw
          BW
        parameter sourceRegister
          Register
        parameter addressingModeSource
          AM
        parameter destinationRegister
          Register
        parameter addressingModeDestination
          AM
        return value
          unit
    *)
    Definition fun_move_inst : Stm [
                                     "bw"  ∷  ty.enum Ebw;
                                     "sourceRegister"  ∷  ty.enum Eregister;
                                     "addressingModeSource"  ∷  ty.enum Eam;
                                     "destinationRegister"  ∷  ty.enum Eregister;
                                     "addressingModeDestination"  ∷  ty.enum Eam
                                   ]
                                   (ty.unit) :=
      stm_let "sourceValue"
              (ty.union Uwordbyte)
              (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                           (_::_)
                                                           ((exp_var "bw"))%exp)
                                                 (_::_)
                                                 ((exp_var "sourceRegister"))%exp)
                                       (_::_)
                                       ((exp_var "addressingModeSource"))%exp))
              (stm_seq (stm_seq (stm_let "ж3688"
                                         (ty.union Uwordbyte)
                                         (stm_let "ж3689"
                                                  (ty.enum Eam)
                                                  (stm_exp (exp_var "addressingModeDestination"))
                                                  (stm_match_enum Eam
                                                                  (stm_exp (exp_var "ж3689"))
                                                                  (fun K => match K with
                                                                            | INDEXED_MODE                => stm_call fetch (env.snoc (env.nil)
                                                                                                                                      (_::_)
                                                                                                                                      ((exp_val (ty.unit) (tt)))%exp)
                                                                            | INDIRECT_AUTOINCREMENT_MODE => stm_exp (exp_union Uwordbyte Kword (exp_val (ty.bvec 16) ([bv 0])))
                                                                            | INDIRECT_REGISTER_MODE      => stm_exp (exp_union Uwordbyte Kword (exp_val (ty.bvec 16) ([bv 0])))
                                                                            | REGISTER_MODE               => stm_exp (exp_union Uwordbyte Kword (exp_val (ty.bvec 16) ([bv 0])))
                                                                            end)))
                                         (stm_write_register LastInstructionFetch (exp_var "ж3688")))
                                (stm_exp (exp_val (ty.unit) (tt))))
                       (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                               (_::_)
                                                                               ((exp_var "bw"))%exp)
                                                                     (_::_)
                                                                     ((exp_var "destinationRegister"))%exp)
                                                           (_::_)
                                                           ((exp_var "addressingModeDestination"))%exp)
                                                 (_::_)
                                                 ((exp_var "sourceValue"))%exp))).
    
    (*
      Extended type
        parameter w1
          WordByte
        parameter w2
          WordByte
        parameter res
          WordByte
        return value
          ?[47]
      
      [0] : Sail type: {('ex12770# : Int) ('ex12773# : Int) ('ex12774# : Int), true. bool('ex12770# < ('ex12773# + 'ex12774#))}
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 455
            Sail position: UnknownLocation
    *)
    Definition fun_hasCarry : Stm [
                                    "w1"  ∷  ty.union Uwordbyte;
                                    "w2"  ∷  ty.union Uwordbyte;
                                    "res"  ∷  ty.union Uwordbyte
                                  ]
                                  (ty.bool) :=
      stm_let "ga#241"
              (ty.int)
              (stm_call unsignedWb (env.snoc (env.nil)
                                             (_::_)
                                             ((exp_var "res"))%exp))
              (stm_let "ga#242"
                       (ty.int)
                       (stm_let "ga#239"
                                (ty.int)
                                (stm_call unsignedWb (env.snoc (env.nil)
                                                               (_::_)
                                                               ((exp_var "w1"))%exp))
                                (stm_let "ga#240"
                                         (ty.int)
                                         (stm_call unsignedWb (env.snoc (env.nil)
                                                                        (_::_)
                                                                        ((exp_var "w2"))%exp))
                                         (stm_exp (((exp_var "ga#239"))+((exp_var "ga#240"))))))
                       (stm_exp (((exp_var "ga#241"))<((exp_var "ga#242"))))).
    
    (*
      Extended type
        parameter w1
          WordByte
        parameter w2
          WordByte
        parameter res
          WordByte
        return value
          ?[48]
      
      [0] : Sail type: {('ex12849# : Int) ('ex12850# : Int) ('ex12851# : Int) ('ex12884# : Int) ('ex12885# : Int) ('ex12886# : Int), true. bool(((('ex12849# < 0 & 'ex12850# < 0) & 'ex12851# > 0) | (('ex12884# > 0 & 'ex12885# > 0) & 'ex12886# < 0)))}
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 455
            Sail position: UnknownLocation
    *)
    Definition fun_hasOverflowAddition : Stm [
                                               "w1"  ∷  ty.union Uwordbyte;
                                               "w2"  ∷  ty.union Uwordbyte;
                                               "res"  ∷  ty.union Uwordbyte
                                             ]
                                             (ty.bool) :=
      stm_let "ga#253"
              (ty.bool)
              (stm_let "ga#247"
                       (ty.bool)
                       (stm_let "ga#243"
                                (ty.int)
                                (stm_call signedWb (env.snoc (env.nil)
                                                             (_::_)
                                                             ((exp_var "w1"))%exp))
                                (stm_exp (((exp_var "ga#243"))<((exp_int 0%Z)))))
                       (stm_let "ж3700"
                                (ty.bool)
                                (stm_exp (exp_var "ga#247"))
                                (stm_if ((stm_exp (exp_var "ж3700")))
                                        (stm_let "ga#246"
                                                 (ty.bool)
                                                 (stm_let "ga#244"
                                                          (ty.int)
                                                          (stm_call signedWb (env.snoc (env.nil)
                                                                                       (_::_)
                                                                                       ((exp_var "w2"))%exp))
                                                          (stm_exp (((exp_var "ga#244"))<((exp_int 0%Z)))))
                                                 (stm_let "ж3699"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#246"))
                                                          (stm_if ((stm_exp (exp_var "ж3699")))
                                                                  (stm_let "ga#245"
                                                                           (ty.int)
                                                                           (stm_call signedWb (env.snoc (env.nil)
                                                                                                        (_::_)
                                                                                                        ((exp_var "res"))%exp))
                                                                           (stm_exp (((exp_var "ga#245"))>((exp_int 0%Z)))))
                                                                  (stm_exp (exp_false)))))
                                        (stm_exp (exp_false)))))
              (stm_let "ж3703"
                       (ty.bool)
                       (stm_exp (exp_var "ga#253"))
                       (stm_if ((stm_exp (exp_var "ж3703")))
                               (stm_exp (exp_true))
                               (stm_let "ga#252"
                                        (ty.bool)
                                        (stm_let "ga#248"
                                                 (ty.int)
                                                 (stm_call signedWb (env.snoc (env.nil)
                                                                              (_::_)
                                                                              ((exp_var "w1"))%exp))
                                                 (stm_exp (((exp_var "ga#248"))>((exp_int 0%Z)))))
                                        (stm_let "ж3702"
                                                 (ty.bool)
                                                 (stm_exp (exp_var "ga#252"))
                                                 (stm_if ((stm_exp (exp_var "ж3702")))
                                                         (stm_let "ga#251"
                                                                  (ty.bool)
                                                                  (stm_let "ga#249"
                                                                           (ty.int)
                                                                           (stm_call signedWb (env.snoc (env.nil)
                                                                                                        (_::_)
                                                                                                        ((exp_var "w2"))%exp))
                                                                           (stm_exp (((exp_var "ga#249"))>((exp_int 0%Z)))))
                                                                  (stm_let "ж3701"
                                                                           (ty.bool)
                                                                           (stm_exp (exp_var "ga#251"))
                                                                           (stm_if ((stm_exp (exp_var "ж3701")))
                                                                                   (stm_let "ga#250"
                                                                                            (ty.int)
                                                                                            (stm_call signedWb (env.snoc (env.nil)
                                                                                                                         (_::_)
                                                                                                                         ((exp_var "res"))%exp))
                                                                                            (stm_exp (((exp_var "ga#250"))<((exp_int 0%Z)))))
                                                                                   (stm_exp (exp_false)))))
                                                         (stm_exp (exp_false))))))).
    
    (*
      Extended type
        parameter w1
          WordByte
        parameter w2
          WordByte
        return value
          WordByte
    *)
    Definition fun_addWithStatusRegister : Stm [
                                                 "w1"  ∷  ty.union Uwordbyte;
                                                 "w2"  ∷  ty.union Uwordbyte
                                               ]
                                               (ty.union Uwordbyte) :=
      stm_let "res"
              (ty.union Uwordbyte)
              (stm_call addBw (env.snoc (env.snoc (env.nil)
                                                  (_::_)
                                                  ((exp_var "w1"))%exp)
                                        (_::_)
                                        ((exp_var "w2"))%exp))
              (stm_seq (stm_let "ga#254"
                                (ty.bool)
                                (stm_call hasCarry (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                 (_::_)
                                                                                 ((exp_var "w1"))%exp)
                                                                       (_::_)
                                                                       ((exp_var "w2"))%exp)
                                                             (_::_)
                                                             ((exp_var "res"))%exp))
                                (stm_let "ж3704"
                                         (ty.bool)
                                         (stm_exp (exp_var "ga#254"))
                                         (stm_if ((stm_exp (exp_var "ж3704")))
                                                 (stm_call setCarrybitTrue (env.snoc (env.nil)
                                                                                     (_::_)
                                                                                     ((exp_val (ty.unit) (tt)))%exp))
                                                 (stm_exp (exp_val (ty.unit) (tt))))))
                       (stm_seq (stm_let "ga#256"
                                         (ty.bool)
                                         (stm_call hasOverflowAddition (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                     (_::_)
                                                                                                     ((exp_var "w1"))%exp)
                                                                                           (_::_)
                                                                                           ((exp_var "w2"))%exp)
                                                                                 (_::_)
                                                                                 ((exp_var "res"))%exp))
                                         (stm_let "ж3706"
                                                  (ty.bool)
                                                  (stm_exp (exp_var "ga#256"))
                                                  (stm_if ((stm_exp (exp_var "ж3706")))
                                                          (stm_call setOverflowbitTrue (env.snoc (env.nil)
                                                                                                 (_::_)
                                                                                                 ((exp_val (ty.unit) (tt)))%exp))
                                                          (stm_exp (exp_val (ty.unit) (tt))))))
                                (stm_exp (exp_var "res")))).
    
    (*
      Extended type
        parameter bw
          BW
        parameter sourceRegister
          Register
        parameter addressingModeSource
          AM
        parameter destinationRegister
          Register
        parameter addressingModeDestination
          AM
        return value
          unit
    *)
    Definition fun_add_inst : Stm [
                                    "bw"  ∷  ty.enum Ebw;
                                    "sourceRegister"  ∷  ty.enum Eregister;
                                    "addressingModeSource"  ∷  ty.enum Eam;
                                    "destinationRegister"  ∷  ty.enum Eregister;
                                    "addressingModeDestination"  ∷  ty.enum Eam
                                  ]
                                  (ty.unit) :=
      stm_seq (stm_call clearStatusRegisters (env.snoc (env.nil)
                                                       (_::_)
                                                       ((exp_val (ty.unit) (tt)))%exp))
              (stm_let "sourceValue"
                       (ty.union Uwordbyte)
                       (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                    (_::_)
                                                                    ((exp_var "bw"))%exp)
                                                          (_::_)
                                                          ((exp_var "sourceRegister"))%exp)
                                                (_::_)
                                                ((exp_var "addressingModeSource"))%exp))
                       (stm_let "destValue"
                                (ty.union Uwordbyte)
                                (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                             (_::_)
                                                                             ((exp_var "bw"))%exp)
                                                                   (_::_)
                                                                   ((exp_var "destinationRegister"))%exp)
                                                         (_::_)
                                                         ((exp_var "addressingModeDestination"))%exp))
                                (stm_let "result"
                                         (ty.union Uwordbyte)
                                         (stm_call addWithStatusRegister (env.snoc (env.snoc (env.nil)
                                                                                             (_::_)
                                                                                             ((exp_var "sourceValue"))%exp)
                                                                                   (_::_)
                                                                                   ((exp_var "destValue"))%exp))
                                         (stm_seq (stm_call setResultStatusRegisters (env.snoc (env.nil)
                                                                                               (_::_)
                                                                                               ((exp_var "result"))%exp))
                                                  (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                          (_::_)
                                                                                                          ((exp_var "bw"))%exp)
                                                                                                (_::_)
                                                                                                ((exp_var "destinationRegister"))%exp)
                                                                                      (_::_)
                                                                                      ((exp_var "addressingModeDestination"))%exp)
                                                                            (_::_)
                                                                            ((exp_var "result"))%exp)))))).
    
    (*
      Extended type
        parameter bw
          BW
        parameter sourceRegister
          Register
        parameter addressingModeSource
          AM
        parameter destinationRegister
          Register
        parameter addressingModeDestination
          AM
        return value
          unit
    *)
    Definition fun_addc_inst : Stm [
                                     "bw"  ∷  ty.enum Ebw;
                                     "sourceRegister"  ∷  ty.enum Eregister;
                                     "addressingModeSource"  ∷  ty.enum Eam;
                                     "destinationRegister"  ∷  ty.enum Eregister;
                                     "addressingModeDestination"  ∷  ty.enum Eam
                                   ]
                                   (ty.unit) :=
      stm_let "sourceValue"
              (ty.union Uwordbyte)
              (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                           (_::_)
                                                           ((exp_var "bw"))%exp)
                                                 (_::_)
                                                 ((exp_var "sourceRegister"))%exp)
                                       (_::_)
                                       ((exp_var "addressingModeSource"))%exp))
              (stm_let "destValue"
                       (ty.union Uwordbyte)
                       (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                    (_::_)
                                                                    ((exp_var "bw"))%exp)
                                                          (_::_)
                                                          ((exp_var "destinationRegister"))%exp)
                                                (_::_)
                                                ((exp_var "addressingModeDestination"))%exp))
                       (stm_let "carry"
                                (ty.union Uwordbyte)
                                (stm_let "ga#263"
                                         (ty.bvec (1))
                                         (stm_call getCarryBit (env.snoc (env.nil)
                                                                         (_::_)
                                                                         ((exp_val (ty.unit) (tt)))%exp))
                                         (stm_call zero_extend_bit_to_byte (env.snoc (env.nil)
                                                                                     (_::_)
                                                                                     ((exp_var "ga#263"))%exp)))
                                (stm_seq (stm_call clearStatusRegisters (env.snoc (env.nil)
                                                                                  (_::_)
                                                                                  ((exp_val (ty.unit) (tt)))%exp))
                                         (stm_let "result"
                                                  (ty.union Uwordbyte)
                                                  (stm_let "ga#262"
                                                           (ty.union Uwordbyte)
                                                           (stm_call addWithStatusRegister (env.snoc (env.snoc (env.nil)
                                                                                                               (_::_)
                                                                                                               ((exp_var "sourceValue"))%exp)
                                                                                                     (_::_)
                                                                                                     ((exp_var "destValue"))%exp))
                                                           (stm_call addWithStatusRegister (env.snoc (env.snoc (env.nil)
                                                                                                               (_::_)
                                                                                                               ((exp_var "ga#262"))%exp)
                                                                                                     (_::_)
                                                                                                     ((exp_var "carry"))%exp)))
                                                  (stm_seq (stm_call setResultStatusRegisters (env.snoc (env.nil)
                                                                                                        (_::_)
                                                                                                        ((exp_var "result"))%exp))
                                                           (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                   (_::_)
                                                                                                                   ((exp_var "bw"))%exp)
                                                                                                         (_::_)
                                                                                                         ((exp_var "destinationRegister"))%exp)
                                                                                               (_::_)
                                                                                               ((exp_var "addressingModeDestination"))%exp)
                                                                                     (_::_)
                                                                                     ((exp_var "result"))%exp))))))).
    
    (*
      Extended type
        parameter bw
          BW
        parameter sourceRegister
          Register
        parameter addressingModeSource
          AM
        parameter destinationRegister
          Register
        parameter addressingModeDestination
          AM
        return value
          unit
    *)
    Definition fun_sub_inst : Stm [
                                    "bw"  ∷  ty.enum Ebw;
                                    "sourceRegister"  ∷  ty.enum Eregister;
                                    "addressingModeSource"  ∷  ty.enum Eam;
                                    "destinationRegister"  ∷  ty.enum Eregister;
                                    "addressingModeDestination"  ∷  ty.enum Eam
                                  ]
                                  (ty.unit) :=
      stm_seq (stm_call clearStatusRegisters (env.snoc (env.nil)
                                                       (_::_)
                                                       ((exp_val (ty.unit) (tt)))%exp))
              (stm_let "sourceValue"
                       (ty.union Uwordbyte)
                       (stm_let "ga#268"
                                (ty.union Uwordbyte)
                                (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                             (_::_)
                                                                             ((exp_var "bw"))%exp)
                                                                   (_::_)
                                                                   ((exp_var "sourceRegister"))%exp)
                                                         (_::_)
                                                         ((exp_var "addressingModeSource"))%exp))
                                (stm_call not_wordByte (env.snoc (env.nil)
                                                                 (_::_)
                                                                 ((exp_var "ga#268"))%exp)))
                       (stm_let "destValue"
                                (ty.union Uwordbyte)
                                (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                             (_::_)
                                                                             ((exp_var "bw"))%exp)
                                                                   (_::_)
                                                                   ((exp_var "destinationRegister"))%exp)
                                                         (_::_)
                                                         ((exp_var "addressingModeDestination"))%exp))
                                (stm_let "result"
                                         (ty.union Uwordbyte)
                                         (stm_let "ga#266"
                                                  (ty.union Uwordbyte)
                                                  (stm_call addWithStatusRegister (env.snoc (env.snoc (env.nil)
                                                                                                      (_::_)
                                                                                                      ((exp_var "sourceValue"))%exp)
                                                                                            (_::_)
                                                                                            ((exp_var "destValue"))%exp))
                                                  (stm_let "ga#267"
                                                           ((ty.union Uwordbyte))
                                                           (stm_exp (exp_union Uwordbyte Kbyte (exp_val (ty.bvec 8) ([bv 1]))))
                                                           (stm_call addWithStatusRegister (env.snoc (env.snoc (env.nil)
                                                                                                               (_::_)
                                                                                                               ((exp_var "ga#266"))%exp)
                                                                                                     (_::_)
                                                                                                     ((exp_var "ga#267"))%exp))))
                                         (stm_seq (stm_call setResultStatusRegisters (env.snoc (env.nil)
                                                                                               (_::_)
                                                                                               ((exp_var "result"))%exp))
                                                  (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                          (_::_)
                                                                                                          ((exp_var "bw"))%exp)
                                                                                                (_::_)
                                                                                                ((exp_var "destinationRegister"))%exp)
                                                                                      (_::_)
                                                                                      ((exp_var "addressingModeDestination"))%exp)
                                                                            (_::_)
                                                                            ((exp_var "result"))%exp)))))).
    
    (*
      Extended type
        parameter bw
          BW
        parameter sourceRegister
          Register
        parameter addressingModeSource
          AM
        parameter destinationRegister
          Register
        parameter addressingModeDestination
          AM
        return value
          unit
    *)
    Definition fun_subc_inst : Stm [
                                     "bw"  ∷  ty.enum Ebw;
                                     "sourceRegister"  ∷  ty.enum Eregister;
                                     "addressingModeSource"  ∷  ty.enum Eam;
                                     "destinationRegister"  ∷  ty.enum Eregister;
                                     "addressingModeDestination"  ∷  ty.enum Eam
                                   ]
                                   (ty.unit) :=
      stm_let "sourceValue"
              (ty.union Uwordbyte)
              (stm_let "ga#273"
                       (ty.union Uwordbyte)
                       (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                    (_::_)
                                                                    ((exp_var "bw"))%exp)
                                                          (_::_)
                                                          ((exp_var "sourceRegister"))%exp)
                                                (_::_)
                                                ((exp_var "addressingModeSource"))%exp))
                       (stm_call not_wordByte (env.snoc (env.nil)
                                                        (_::_)
                                                        ((exp_var "ga#273"))%exp)))
              (stm_let "destValue"
                       (ty.union Uwordbyte)
                       (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                    (_::_)
                                                                    ((exp_var "bw"))%exp)
                                                          (_::_)
                                                          ((exp_var "destinationRegister"))%exp)
                                                (_::_)
                                                ((exp_var "addressingModeDestination"))%exp))
                       (stm_let "carry"
                                (ty.union Uwordbyte)
                                (stm_let "ga#272"
                                         (ty.bvec (1))
                                         (stm_call getCarryBit (env.snoc (env.nil)
                                                                         (_::_)
                                                                         ((exp_val (ty.unit) (tt)))%exp))
                                         (stm_call zero_extend_bit_to_byte (env.snoc (env.nil)
                                                                                     (_::_)
                                                                                     ((exp_var "ga#272"))%exp)))
                                (stm_seq (stm_call clearStatusRegisters (env.snoc (env.nil)
                                                                                  (_::_)
                                                                                  ((exp_val (ty.unit) (tt)))%exp))
                                         (stm_let "result"
                                                  (ty.union Uwordbyte)
                                                  (stm_let "ga#271"
                                                           (ty.union Uwordbyte)
                                                           (stm_call addWithStatusRegister (env.snoc (env.snoc (env.nil)
                                                                                                               (_::_)
                                                                                                               ((exp_var "sourceValue"))%exp)
                                                                                                     (_::_)
                                                                                                     ((exp_var "destValue"))%exp))
                                                           (stm_call addWithStatusRegister (env.snoc (env.snoc (env.nil)
                                                                                                               (_::_)
                                                                                                               ((exp_var "ga#271"))%exp)
                                                                                                     (_::_)
                                                                                                     ((exp_var "carry"))%exp)))
                                                  (stm_seq (stm_call setResultStatusRegisters (env.snoc (env.nil)
                                                                                                        (_::_)
                                                                                                        ((exp_var "result"))%exp))
                                                           (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                   (_::_)
                                                                                                                   ((exp_var "bw"))%exp)
                                                                                                         (_::_)
                                                                                                         ((exp_var "destinationRegister"))%exp)
                                                                                               (_::_)
                                                                                               ((exp_var "addressingModeDestination"))%exp)
                                                                                     (_::_)
                                                                                     ((exp_var "result"))%exp))))))).
    
    (*
      Extended type
        parameter bw
          BW
        parameter sourceRegister
          Register
        parameter addressingModeSource
          AM
        parameter destinationRegister
          Register
        parameter addressingModeDestination
          AM
        return value
          unit
    *)
    Definition fun_cmp_inst : Stm [
                                    "bw"  ∷  ty.enum Ebw;
                                    "sourceRegister"  ∷  ty.enum Eregister;
                                    "addressingModeSource"  ∷  ty.enum Eam;
                                    "destinationRegister"  ∷  ty.enum Eregister;
                                    "addressingModeDestination"  ∷  ty.enum Eam
                                  ]
                                  (ty.unit) :=
      stm_seq (stm_call clearStatusRegisters (env.snoc (env.nil)
                                                       (_::_)
                                                       ((exp_val (ty.unit) (tt)))%exp))
              (stm_let "sourceValue"
                       (ty.union Uwordbyte)
                       (stm_let "ga#277"
                                (ty.union Uwordbyte)
                                (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                             (_::_)
                                                                             ((exp_var "bw"))%exp)
                                                                   (_::_)
                                                                   ((exp_var "sourceRegister"))%exp)
                                                         (_::_)
                                                         ((exp_var "addressingModeSource"))%exp))
                                (stm_call not_wordByte (env.snoc (env.nil)
                                                                 (_::_)
                                                                 ((exp_var "ga#277"))%exp)))
                       (stm_let "destValue"
                                (ty.union Uwordbyte)
                                (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                             (_::_)
                                                                             ((exp_var "bw"))%exp)
                                                                   (_::_)
                                                                   ((exp_var "destinationRegister"))%exp)
                                                         (_::_)
                                                         ((exp_var "addressingModeDestination"))%exp))
                                (stm_let "result"
                                         (ty.union Uwordbyte)
                                         (stm_let "ga#275"
                                                  (ty.union Uwordbyte)
                                                  (stm_call addWithStatusRegister (env.snoc (env.snoc (env.nil)
                                                                                                      (_::_)
                                                                                                      ((exp_var "sourceValue"))%exp)
                                                                                            (_::_)
                                                                                            ((exp_var "destValue"))%exp))
                                                  (stm_let "ga#276"
                                                           ((ty.union Uwordbyte))
                                                           (stm_exp (exp_union Uwordbyte Kbyte (exp_val (ty.bvec 8) ([bv 1]))))
                                                           (stm_call addWithStatusRegister (env.snoc (env.snoc (env.nil)
                                                                                                               (_::_)
                                                                                                               ((exp_var "ga#275"))%exp)
                                                                                                     (_::_)
                                                                                                     ((exp_var "ga#276"))%exp))))
                                         (stm_call setResultStatusRegisters (env.snoc (env.nil)
                                                                                      (_::_)
                                                                                      ((exp_var "result"))%exp))))).
    
    (*
      Extended type
        parameter w1
          WordByte
        parameter w2
          WordByte
        return value
          WordByte
    *)
    Definition fun_andWithStatusRegister : Stm [
                                                 "w1"  ∷  ty.union Uwordbyte;
                                                 "w2"  ∷  ty.union Uwordbyte
                                               ]
                                               (ty.union Uwordbyte) :=
      stm_let "res"
              (ty.union Uwordbyte)
              (stm_call and_wordByte (env.snoc (env.snoc (env.nil)
                                                         (_::_)
                                                         ((exp_var "w1"))%exp)
                                               (_::_)
                                               ((exp_var "w2"))%exp))
              (stm_seq (stm_let "ga#278"
                                (ty.bool)
                                (stm_call isNegative (env.snoc (env.nil)
                                                               (_::_)
                                                               ((exp_var "res"))%exp))
                                (stm_let "ж3739"
                                         (ty.bool)
                                         (stm_exp (exp_var "ga#278"))
                                         (stm_if ((stm_exp (exp_var "ж3739")))
                                                 (stm_call setNegativebitTrue (env.snoc (env.nil)
                                                                                        (_::_)
                                                                                        ((exp_val (ty.unit) (tt)))%exp))
                                                 (stm_exp (exp_val (ty.unit) (tt))))))
                       (stm_seq (stm_let "ga#280"
                                         (ty.bool)
                                         (stm_call isZero (env.snoc (env.nil)
                                                                    (_::_)
                                                                    ((exp_var "res"))%exp))
                                         (stm_let "ж3741"
                                                  (ty.bool)
                                                  (stm_exp (exp_var "ga#280"))
                                                  (stm_if ((stm_exp (exp_var "ж3741")))
                                                          (stm_call setZerobitTrue (env.snoc (env.nil)
                                                                                             (_::_)
                                                                                             ((exp_val (ty.unit) (tt)))%exp))
                                                          (stm_exp (exp_val (ty.unit) (tt))))))
                                (stm_seq (stm_let "ga#283"
                                                  (ty.bool)
                                                  (stm_let "ga#282"
                                                           (ty.bool)
                                                           (stm_call isZero (env.snoc (env.nil)
                                                                                      (_::_)
                                                                                      ((exp_var "res"))%exp))
                                                           (stm_exp (exp_unop uop.not (exp_var "ga#282"))))
                                                  (stm_let "ж3743"
                                                           (ty.bool)
                                                           (stm_exp (exp_var "ga#283"))
                                                           (stm_if ((stm_exp (exp_var "ж3743")))
                                                                   (stm_call setCarrybitTrue (env.snoc (env.nil)
                                                                                                       (_::_)
                                                                                                       ((exp_val (ty.unit) (tt)))%exp))
                                                                   (stm_exp (exp_val (ty.unit) (tt))))))
                                         (stm_exp (exp_var "res"))))).
    
    (*
      Extended type
        parameter bw
          BW
        parameter sourceRegister
          Register
        parameter addressingModeSource
          AM
        parameter destinationRegister
          Register
        parameter addressingModeDestination
          AM
        return value
          unit
    *)
    Definition fun_and_inst : Stm [
                                    "bw"  ∷  ty.enum Ebw;
                                    "sourceRegister"  ∷  ty.enum Eregister;
                                    "addressingModeSource"  ∷  ty.enum Eam;
                                    "destinationRegister"  ∷  ty.enum Eregister;
                                    "addressingModeDestination"  ∷  ty.enum Eam
                                  ]
                                  (ty.unit) :=
      stm_seq (stm_call clearStatusRegisters (env.snoc (env.nil)
                                                       (_::_)
                                                       ((exp_val (ty.unit) (tt)))%exp))
              (stm_let "sourceValue"
                       (ty.union Uwordbyte)
                       (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                    (_::_)
                                                                    ((exp_var "bw"))%exp)
                                                          (_::_)
                                                          ((exp_var "sourceRegister"))%exp)
                                                (_::_)
                                                ((exp_var "addressingModeSource"))%exp))
                       (stm_let "destValue"
                                (ty.union Uwordbyte)
                                (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                             (_::_)
                                                                             ((exp_var "bw"))%exp)
                                                                   (_::_)
                                                                   ((exp_var "destinationRegister"))%exp)
                                                         (_::_)
                                                         ((exp_var "addressingModeDestination"))%exp))
                                (stm_let "result"
                                         (ty.union Uwordbyte)
                                         (stm_call andWithStatusRegister (env.snoc (env.snoc (env.nil)
                                                                                             (_::_)
                                                                                             ((exp_var "sourceValue"))%exp)
                                                                                   (_::_)
                                                                                   ((exp_var "destValue"))%exp))
                                         (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                 (_::_)
                                                                                                 ((exp_var "bw"))%exp)
                                                                                       (_::_)
                                                                                       ((exp_var "destinationRegister"))%exp)
                                                                             (_::_)
                                                                             ((exp_var "addressingModeDestination"))%exp)
                                                                   (_::_)
                                                                   ((exp_var "result"))%exp))))).
    
    (*
      Extended type
        parameter w1
          WordByte
        parameter w2
          WordByte
        return value
          WordByte
    *)
    Definition fun_xorWithStatusRegister : Stm [
                                                 "w1"  ∷  ty.union Uwordbyte;
                                                 "w2"  ∷  ty.union Uwordbyte
                                               ]
                                               (ty.union Uwordbyte) :=
      stm_let "res"
              (ty.union Uwordbyte)
              (stm_call xor_wordByte (env.snoc (env.snoc (env.nil)
                                                         (_::_)
                                                         ((exp_var "w1"))%exp)
                                               (_::_)
                                               ((exp_var "w2"))%exp))
              (stm_seq (stm_let "ga#286"
                                (ty.bool)
                                (stm_call isNegative (env.snoc (env.nil)
                                                               (_::_)
                                                               ((exp_var "res"))%exp))
                                (stm_let "ж3754"
                                         (ty.bool)
                                         (stm_exp (exp_var "ga#286"))
                                         (stm_if ((stm_exp (exp_var "ж3754")))
                                                 (stm_call setNegativebitTrue (env.snoc (env.nil)
                                                                                        (_::_)
                                                                                        ((exp_val (ty.unit) (tt)))%exp))
                                                 (stm_exp (exp_val (ty.unit) (tt))))))
                       (stm_seq (stm_let "ga#288"
                                         (ty.bool)
                                         (stm_call isZero (env.snoc (env.nil)
                                                                    (_::_)
                                                                    ((exp_var "res"))%exp))
                                         (stm_let "ж3756"
                                                  (ty.bool)
                                                  (stm_exp (exp_var "ga#288"))
                                                  (stm_if ((stm_exp (exp_var "ж3756")))
                                                          (stm_call setZerobitTrue (env.snoc (env.nil)
                                                                                             (_::_)
                                                                                             ((exp_val (ty.unit) (tt)))%exp))
                                                          (stm_exp (exp_val (ty.unit) (tt))))))
                                (stm_seq (stm_let "ga#291"
                                                  (ty.bool)
                                                  (stm_let "ga#290"
                                                           (ty.bool)
                                                           (stm_call isZero (env.snoc (env.nil)
                                                                                      (_::_)
                                                                                      ((exp_var "res"))%exp))
                                                           (stm_exp (exp_unop uop.not (exp_var "ga#290"))))
                                                  (stm_let "ж3758"
                                                           (ty.bool)
                                                           (stm_exp (exp_var "ga#291"))
                                                           (stm_if ((stm_exp (exp_var "ж3758")))
                                                                   (stm_call setCarrybitTrue (env.snoc (env.nil)
                                                                                                       (_::_)
                                                                                                       ((exp_val (ty.unit) (tt)))%exp))
                                                                   (stm_exp (exp_val (ty.unit) (tt))))))
                                         (stm_seq (stm_let "ga#294"
                                                           (ty.bool)
                                                           (stm_let "ga#293"
                                                                    (ty.bool)
                                                                    (stm_call isNegative (env.snoc (env.nil)
                                                                                                   (_::_)
                                                                                                   ((exp_var "w1"))%exp))
                                                                    (stm_let "ж3760"
                                                                             (ty.bool)
                                                                             (stm_exp (exp_var "ga#293"))
                                                                             (stm_if ((stm_exp (exp_var "ж3760")))
                                                                                     (stm_call isNegative (env.snoc (env.nil)
                                                                                                                    (_::_)
                                                                                                                    ((exp_var "w2"))%exp))
                                                                                     (stm_exp (exp_false)))))
                                                           (stm_let "ж3761"
                                                                    (ty.bool)
                                                                    (stm_exp (exp_var "ga#294"))
                                                                    (stm_if ((stm_exp (exp_var "ж3761")))
                                                                            (stm_call setOverflowbitTrue (env.snoc (env.nil)
                                                                                                                   (_::_)
                                                                                                                   ((exp_val (ty.unit) (tt)))%exp))
                                                                            (stm_exp (exp_val (ty.unit) (tt))))))
                                                  (stm_exp (exp_var "res")))))).
    
    (*
      Extended type
        parameter bw
          BW
        parameter sourceRegister
          Register
        parameter addressingModeSource
          AM
        parameter destinationRegister
          Register
        parameter addressingModeDestination
          AM
        return value
          unit
    *)
    Definition fun_xor_inst : Stm [
                                    "bw"  ∷  ty.enum Ebw;
                                    "sourceRegister"  ∷  ty.enum Eregister;
                                    "addressingModeSource"  ∷  ty.enum Eam;
                                    "destinationRegister"  ∷  ty.enum Eregister;
                                    "addressingModeDestination"  ∷  ty.enum Eam
                                  ]
                                  (ty.unit) :=
      stm_seq (stm_call clearStatusRegisters (env.snoc (env.nil)
                                                       (_::_)
                                                       ((exp_val (ty.unit) (tt)))%exp))
              (stm_let "sourceValue"
                       (ty.union Uwordbyte)
                       (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                    (_::_)
                                                                    ((exp_var "bw"))%exp)
                                                          (_::_)
                                                          ((exp_var "sourceRegister"))%exp)
                                                (_::_)
                                                ((exp_var "addressingModeSource"))%exp))
                       (stm_let "destValue"
                                (ty.union Uwordbyte)
                                (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                             (_::_)
                                                                             ((exp_var "bw"))%exp)
                                                                   (_::_)
                                                                   ((exp_var "destinationRegister"))%exp)
                                                         (_::_)
                                                         ((exp_var "addressingModeDestination"))%exp))
                                (stm_let "result"
                                         (ty.union Uwordbyte)
                                         (stm_call xorWithStatusRegister (env.snoc (env.snoc (env.nil)
                                                                                             (_::_)
                                                                                             ((exp_var "sourceValue"))%exp)
                                                                                   (_::_)
                                                                                   ((exp_var "destValue"))%exp))
                                         (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                 (_::_)
                                                                                                 ((exp_var "bw"))%exp)
                                                                                       (_::_)
                                                                                       ((exp_var "destinationRegister"))%exp)
                                                                             (_::_)
                                                                             ((exp_var "addressingModeDestination"))%exp)
                                                                   (_::_)
                                                                   ((exp_var "result"))%exp))))).
    
    (*
      Extended type
        parameter bw
          BW
        parameter sourceRegister
          Register
        parameter addressingModeSource
          AM
        parameter destinationRegister
          Register
        parameter addressingModeDestination
          AM
        return value
          unit
    *)
    Definition fun_bic_inst : Stm [
                                    "bw"  ∷  ty.enum Ebw;
                                    "sourceRegister"  ∷  ty.enum Eregister;
                                    "addressingModeSource"  ∷  ty.enum Eam;
                                    "destinationRegister"  ∷  ty.enum Eregister;
                                    "addressingModeDestination"  ∷  ty.enum Eam
                                  ]
                                  (ty.unit) :=
      stm_let "sourceValue"
              (ty.union Uwordbyte)
              (stm_let "ga#297"
                       (ty.union Uwordbyte)
                       (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                    (_::_)
                                                                    ((exp_var "bw"))%exp)
                                                          (_::_)
                                                          ((exp_var "sourceRegister"))%exp)
                                                (_::_)
                                                ((exp_var "addressingModeSource"))%exp))
                       (stm_call not_wordByte (env.snoc (env.nil)
                                                        (_::_)
                                                        ((exp_var "ga#297"))%exp)))
              (stm_let "destValue"
                       (ty.union Uwordbyte)
                       (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                    (_::_)
                                                                    ((exp_var "bw"))%exp)
                                                          (_::_)
                                                          ((exp_var "destinationRegister"))%exp)
                                                (_::_)
                                                ((exp_var "addressingModeDestination"))%exp))
                       (stm_let "result"
                                (ty.union Uwordbyte)
                                (stm_call and_wordByte (env.snoc (env.snoc (env.nil)
                                                                           (_::_)
                                                                           ((exp_var "sourceValue"))%exp)
                                                                 (_::_)
                                                                 ((exp_var "destValue"))%exp))
                                (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                        (_::_)
                                                                                        ((exp_var "bw"))%exp)
                                                                              (_::_)
                                                                              ((exp_var "destinationRegister"))%exp)
                                                                    (_::_)
                                                                    ((exp_var "addressingModeDestination"))%exp)
                                                          (_::_)
                                                          ((exp_var "result"))%exp)))).
    
    (*
      Extended type
        parameter bw
          BW
        parameter sourceRegister
          Register
        parameter addressingModeSource
          AM
        parameter destinationRegister
          Register
        parameter addressingModeDestination
          AM
        return value
          unit
    *)
    Definition fun_bis_inst : Stm [
                                    "bw"  ∷  ty.enum Ebw;
                                    "sourceRegister"  ∷  ty.enum Eregister;
                                    "addressingModeSource"  ∷  ty.enum Eam;
                                    "destinationRegister"  ∷  ty.enum Eregister;
                                    "addressingModeDestination"  ∷  ty.enum Eam
                                  ]
                                  (ty.unit) :=
      stm_let "sourceValue"
              (ty.union Uwordbyte)
              (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                           (_::_)
                                                           ((exp_var "bw"))%exp)
                                                 (_::_)
                                                 ((exp_var "sourceRegister"))%exp)
                                       (_::_)
                                       ((exp_var "addressingModeSource"))%exp))
              (stm_let "destValue"
                       (ty.union Uwordbyte)
                       (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                    (_::_)
                                                                    ((exp_var "bw"))%exp)
                                                          (_::_)
                                                          ((exp_var "destinationRegister"))%exp)
                                                (_::_)
                                                ((exp_var "addressingModeDestination"))%exp))
                       (stm_let "result"
                                (ty.union Uwordbyte)
                                (stm_call or_wordByte (env.snoc (env.snoc (env.nil)
                                                                          (_::_)
                                                                          ((exp_var "sourceValue"))%exp)
                                                                (_::_)
                                                                ((exp_var "destValue"))%exp))
                                (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                        (_::_)
                                                                                        ((exp_var "bw"))%exp)
                                                                              (_::_)
                                                                              ((exp_var "destinationRegister"))%exp)
                                                                    (_::_)
                                                                    ((exp_var "addressingModeDestination"))%exp)
                                                          (_::_)
                                                          ((exp_var "result"))%exp)))).
    
    (*
      Extended type
        parameter bw
          BW
        parameter sourceRegister
          Register
        parameter addressingModeSource
          AM
        parameter destinationRegister
          Register
        parameter addressingModeDestination
          AM
        return value
          unit
    *)
    Definition fun_bit_inst : Stm [
                                    "bw"  ∷  ty.enum Ebw;
                                    "sourceRegister"  ∷  ty.enum Eregister;
                                    "addressingModeSource"  ∷  ty.enum Eam;
                                    "destinationRegister"  ∷  ty.enum Eregister;
                                    "addressingModeDestination"  ∷  ty.enum Eam
                                  ]
                                  (ty.unit) :=
      stm_let "sourceValue"
              (ty.union Uwordbyte)
              (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                           (_::_)
                                                           ((exp_var "bw"))%exp)
                                                 (_::_)
                                                 ((exp_var "sourceRegister"))%exp)
                                       (_::_)
                                       ((exp_var "addressingModeSource"))%exp))
              (stm_let "destValue"
                       (ty.union Uwordbyte)
                       (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                    (_::_)
                                                                    ((exp_var "bw"))%exp)
                                                          (_::_)
                                                          ((exp_var "destinationRegister"))%exp)
                                                (_::_)
                                                ((exp_var "addressingModeDestination"))%exp))
                       (stm_let "ga#298"
                                (ty.union Uwordbyte)
                                (stm_call andWithStatusRegister (env.snoc (env.snoc (env.nil)
                                                                                    (_::_)
                                                                                    ((exp_var "sourceValue"))%exp)
                                                                          (_::_)
                                                                          ((exp_var "destValue"))%exp))
                                (stm_seq (stm_exp (exp_var "ga#298"))
                                         (stm_exp (exp_val (ty.unit) (tt)))))).
    
    (*
      Extended type
        parameter merge#var
          WordByte
        return value
          $0
    *)
    Definition fun_asDecimal : Stm [
                                     "merge#var"  ∷  ty.union Uwordbyte
                                   ]
                                   (ty.int) :=
      stm_let "ж3777"
              (ty.union Uwordbyte)
              (stm_exp (exp_var "merge#var"))
              (stm_match_union_alt_list Uwordbyte
                                        (stm_exp (exp_var "ж3777"))
                                        [
                                          existT Kbyte (MkAlt (pat_var "v__1") (stm_seq (stm_exp (exp_unop (uop.vector_subrange 4 4) (exp_var "v__1")))
                                                                                        (stm_let "b"
                                                                                                 (ty.bvec (4))
                                                                                                 (stm_exp (exp_unop (uop.vector_subrange 0 4) (exp_var "v__1")))
                                                                                                 (stm_let "a"
                                                                                                          (ty.bvec (4))
                                                                                                          (stm_exp (exp_unop (uop.vector_subrange 4 4) (exp_var "v__1")))
                                                                                                          (stm_let "ga#309"
                                                                                                                   (ty.int)
                                                                                                                   (stm_let "ga#308"
                                                                                                                            (ty.int)
                                                                                                                            (stm_exp (exp_unop uop.unsigned (exp_var "a")))
                                                                                                                            (stm_exp (((exp_var "ga#308"))*((exp_int 10%Z)))))
                                                                                                                   (stm_let "ga#310"
                                                                                                                            (ty.int)
                                                                                                                            (stm_exp (exp_unop uop.unsigned (exp_var "b")))
                                                                                                                            (stm_exp (((exp_var "ga#309"))+((exp_var "ga#310"))))))))));
                                          existT Kword (MkAlt (pat_var "v__0") (stm_seq (stm_exp (exp_unop (uop.vector_subrange 12 4) (exp_var "v__0")))
                                                                                        (stm_let "d"
                                                                                                 (ty.bvec (4))
                                                                                                 (stm_exp (exp_unop (uop.vector_subrange 0 4) (exp_var "v__0")))
                                                                                                 (stm_let "c"
                                                                                                          (ty.bvec (4))
                                                                                                          (stm_exp (exp_unop (uop.vector_subrange 4 4) (exp_var "v__0")))
                                                                                                          (stm_let "b"
                                                                                                                   (ty.bvec (4))
                                                                                                                   (stm_exp (exp_unop (uop.vector_subrange 8 4) (exp_var "v__0")))
                                                                                                                   (stm_let "a"
                                                                                                                            (ty.bvec (4))
                                                                                                                            (stm_exp (exp_unop (uop.vector_subrange 12 4) (exp_var "v__0")))
                                                                                                                            (stm_let "ga#306"
                                                                                                                                     (ty.int)
                                                                                                                                     (stm_let "ga#304"
                                                                                                                                              (ty.int)
                                                                                                                                              (stm_let "ga#301"
                                                                                                                                                       (ty.int)
                                                                                                                                                       (stm_let "ga#299"
                                                                                                                                                                (ty.int)
                                                                                                                                                                (stm_exp (exp_unop uop.unsigned (exp_var "a")))
                                                                                                                                                                (stm_exp (((exp_var "ga#299"))*((exp_int 1000%Z)))))
                                                                                                                                                       (stm_let "ga#302"
                                                                                                                                                                (ty.int)
                                                                                                                                                                (stm_let "ga#300"
                                                                                                                                                                         (ty.int)
                                                                                                                                                                         (stm_exp (exp_unop uop.unsigned (exp_var "b")))
                                                                                                                                                                         (stm_exp (((exp_var "ga#300"))*((exp_int 100%Z)))))
                                                                                                                                                                (stm_exp (((exp_var "ga#301"))+((exp_var "ga#302"))))))
                                                                                                                                              (stm_let "ga#305"
                                                                                                                                                       (ty.int)
                                                                                                                                                       (stm_let "ga#303"
                                                                                                                                                                (ty.int)
                                                                                                                                                                (stm_exp (exp_unop uop.unsigned (exp_var "c")))
                                                                                                                                                                (stm_exp (((exp_var "ga#303"))*((exp_int 10%Z)))))
                                                                                                                                                       (stm_exp (((exp_var "ga#304"))+((exp_var "ga#305"))))))
                                                                                                                                     (stm_let "ga#307"
                                                                                                                                              (ty.int)
                                                                                                                                              (stm_exp (exp_unop uop.unsigned (exp_var "d")))
                                                                                                                                              (stm_exp (((exp_var "ga#306"))+((exp_var "ga#307"))))))))))))
                                        ]
                                        Logic.I).
    
    (*
      Extended type
        parameter number
          int($0)
        return value
          WordByte
    *)
    Definition fun_asWordByte : Stm [
                                      "number"  ∷  ty.int
                                    ]
                                    (ty.union Uwordbyte) :=
      stm_seq (stm_exp (exp_union Uexception Knotimplemented (exp_string "katamaran doesn't support integer / and %")))
              (stm_fail (ty.union Uwordbyte) "failure").
    
    (*
      Extended type
        parameter bw
          BW
        parameter sourceRegister
          Register
        parameter addressingModeSource
          AM
        parameter destinationRegister
          Register
        parameter addressingModeDestination
          AM
        return value
          unit
    *)
    Definition fun_dadd_inst : Stm [
                                     "bw"  ∷  ty.enum Ebw;
                                     "sourceRegister"  ∷  ty.enum Eregister;
                                     "addressingModeSource"  ∷  ty.enum Eam;
                                     "destinationRegister"  ∷  ty.enum Eregister;
                                     "addressingModeDestination"  ∷  ty.enum Eam
                                   ]
                                   (ty.unit) :=
      stm_let "sourceValue"
              (ty.int)
              (stm_let "ga#322"
                       (ty.union Uwordbyte)
                       (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                    (_::_)
                                                                    ((exp_var "bw"))%exp)
                                                          (_::_)
                                                          ((exp_var "sourceRegister"))%exp)
                                                (_::_)
                                                ((exp_var "addressingModeSource"))%exp))
                       (stm_call asDecimal (env.snoc (env.nil)
                                                     (_::_)
                                                     ((exp_var "ga#322"))%exp)))
              (stm_let "destValue"
                       (ty.int)
                       (stm_let "ga#321"
                                (ty.union Uwordbyte)
                                (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                             (_::_)
                                                                             ((exp_var "bw"))%exp)
                                                                   (_::_)
                                                                   ((exp_var "destinationRegister"))%exp)
                                                         (_::_)
                                                         ((exp_var "addressingModeDestination"))%exp))
                                (stm_call asDecimal (env.snoc (env.nil)
                                                              (_::_)
                                                              ((exp_var "ga#321"))%exp)))
                       (stm_let "res"
                                (ty.union Uwordbyte)
                                (stm_let "ga#320"
                                         (ty.int)
                                         (stm_exp (((exp_var "sourceValue"))+((exp_var "destValue"))))
                                         (stm_call asWordByte (env.snoc (env.nil)
                                                                        (_::_)
                                                                        ((exp_var "ga#320"))%exp)))
                                (stm_seq (stm_let "ga#312"
                                                  (ty.bool)
                                                  (stm_call isNegative (env.snoc (env.nil)
                                                                                 (_::_)
                                                                                 ((exp_var "res"))%exp))
                                                  (stm_let "ж3783"
                                                           (ty.bool)
                                                           (stm_exp (exp_var "ga#312"))
                                                           (stm_if ((stm_exp (exp_var "ж3783")))
                                                                   (stm_call setNegativebitTrue (env.snoc (env.nil)
                                                                                                          (_::_)
                                                                                                          ((exp_val (ty.unit) (tt)))%exp))
                                                                   (stm_exp (exp_val (ty.unit) (tt))))))
                                         (stm_seq (stm_let "ga#314"
                                                           (ty.bool)
                                                           (stm_call isZero (env.snoc (env.nil)
                                                                                      (_::_)
                                                                                      ((exp_var "res"))%exp))
                                                           (stm_let "ж3785"
                                                                    (ty.bool)
                                                                    (stm_exp (exp_var "ga#314"))
                                                                    (stm_if ((stm_exp (exp_var "ж3785")))
                                                                            (stm_call setZerobitTrue (env.snoc (env.nil)
                                                                                                               (_::_)
                                                                                                               ((exp_val (ty.unit) (tt)))%exp))
                                                                            (stm_exp (exp_val (ty.unit) (tt))))))
                                                  (stm_let "ж3787"
                                                           (ty.enum Ebw)
                                                           (stm_exp (exp_var "bw"))
                                                           (stm_match_enum Ebw
                                                                           (stm_exp (exp_var "ж3787"))
                                                                           (fun K => match K with
                                                                                     | BYTE_INSTRUCTION => stm_let "ga#317"
                                                                                                                   (ty.bool)
                                                                                                                   (stm_let "ga#316"
                                                                                                                            (ty.int)
                                                                                                                            (stm_exp (((exp_var "sourceValue"))+((exp_var "destValue"))))
                                                                                                                            (stm_exp (((exp_var "ga#316"))>((exp_int 99%Z)))))
                                                                                                                   (stm_let "ж3788"
                                                                                                                            (ty.bool)
                                                                                                                            (stm_exp (exp_var "ga#317"))
                                                                                                                            (stm_if ((stm_exp (exp_var "ж3788")))
                                                                                                                                    (stm_call setCarrybitTrue (env.snoc (env.nil)
                                                                                                                                                                        (_::_)
                                                                                                                                                                        ((exp_val (ty.unit) (tt)))%exp))
                                                                                                                                    (stm_exp (exp_val (ty.unit) (tt)))))
                                                                                     | WORD_INSTRUCTION => stm_let "ga#319"
                                                                                                                   (ty.bool)
                                                                                                                   (stm_let "ga#318"
                                                                                                                            (ty.int)
                                                                                                                            (stm_exp (((exp_var "sourceValue"))+((exp_var "destValue"))))
                                                                                                                            (stm_exp (((exp_var "ga#318"))>((exp_int 9999%Z)))))
                                                                                                                   (stm_let "ж3789"
                                                                                                                            (ty.bool)
                                                                                                                            (stm_exp (exp_var "ga#319"))
                                                                                                                            (stm_if ((stm_exp (exp_var "ж3789")))
                                                                                                                                    (stm_call setCarrybitTrue (env.snoc (env.nil)
                                                                                                                                                                        (_::_)
                                                                                                                                                                        ((exp_val (ty.unit) (tt)))%exp))
                                                                                                                                    (stm_exp (exp_val (ty.unit) (tt)))))
                                                                                     end))))))).
    
    (*
      Extended type
        parameter arg#
          doubleop
        return value
          ?[49]
      
      [0] : Sail type: bitvector(4)
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_encdec_doubleop_forwards : Stm [
                                                    "arg#"  ∷  ty.enum Edoubleop
                                                  ]
                                                  (ty.bvec (4)) :=
      stm_let "ж3797"
              (ty.enum Edoubleop)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Edoubleop
                              (stm_exp (exp_var "ж3797"))
                              (fun K => match K with
                                        | ADD  => stm_exp (exp_val (ty.bvec 4) ([bv 5]))
                                        | ADDC => stm_exp (exp_val (ty.bvec 4) ([bv 6]))
                                        | AND  => stm_exp (exp_val (ty.bvec 4) ([bv 15]))
                                        | BIC  => stm_exp (exp_val (ty.bvec 4) ([bv 12]))
                                        | BIS  => stm_exp (exp_val (ty.bvec 4) ([bv 13]))
                                        | BIT  => stm_exp (exp_val (ty.bvec 4) ([bv 11]))
                                        | CMP  => stm_exp (exp_val (ty.bvec 4) ([bv 9]))
                                        | DADD => stm_exp (exp_val (ty.bvec 4) ([bv 10]))
                                        | MOV  => stm_exp (exp_val (ty.bvec 4) ([bv 4]))
                                        | SUB  => stm_exp (exp_val (ty.bvec 4) ([bv 7]))
                                        | SUBC => stm_exp (exp_val (ty.bvec 4) ([bv 8]))
                                        | XOR  => stm_exp (exp_val (ty.bvec 4) ([bv 14]))
                                        end)).
    
    (*
      Extended type
        parameter arg#
          ?[50:4]
        return value
          doubleop
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_encdec_doubleop_backwards : Stm [
                                                     "arg#"  ∷  ty.bvec (4)
                                                   ]
                                                   (ty.enum Edoubleop) :=
      stm_let "b__0"
              (ty.bvec (4))
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#323"
                       (ty.bool)
                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 4])))))
                       (stm_let "ж3825"
                                (ty.bool)
                                (stm_exp (exp_var "ga#323"))
                                (stm_if ((stm_exp (exp_var "ж3825")))
                                        (stm_exp (exp_val (ty.enum Edoubleop) (MOV)))
                                        (stm_let "ga#324"
                                                 (ty.bool)
                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 5])))))
                                                 (stm_let "ж3824"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#324"))
                                                          (stm_if ((stm_exp (exp_var "ж3824")))
                                                                  (stm_exp (exp_val (ty.enum Edoubleop) (ADD)))
                                                                  (stm_let "ga#325"
                                                                           (ty.bool)
                                                                           (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 6])))))
                                                                           (stm_let "ж3823"
                                                                                    (ty.bool)
                                                                                    (stm_exp (exp_var "ga#325"))
                                                                                    (stm_if ((stm_exp (exp_var "ж3823")))
                                                                                            (stm_exp (exp_val (ty.enum Edoubleop) (ADDC)))
                                                                                            (stm_let "ga#326"
                                                                                                     (ty.bool)
                                                                                                     (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 7])))))
                                                                                                     (stm_let "ж3822"
                                                                                                              (ty.bool)
                                                                                                              (stm_exp (exp_var "ga#326"))
                                                                                                              (stm_if ((stm_exp (exp_var "ж3822")))
                                                                                                                      (stm_exp (exp_val (ty.enum Edoubleop) (SUB)))
                                                                                                                      (stm_let "ga#327"
                                                                                                                               (ty.bool)
                                                                                                                               (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 8])))))
                                                                                                                               (stm_let "ж3821"
                                                                                                                                        (ty.bool)
                                                                                                                                        (stm_exp (exp_var "ga#327"))
                                                                                                                                        (stm_if ((stm_exp (exp_var "ж3821")))
                                                                                                                                                (stm_exp (exp_val (ty.enum Edoubleop) (SUBC)))
                                                                                                                                                (stm_let "ga#328"
                                                                                                                                                         (ty.bool)
                                                                                                                                                         (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 9])))))
                                                                                                                                                         (stm_let "ж3820"
                                                                                                                                                                  (ty.bool)
                                                                                                                                                                  (stm_exp (exp_var "ga#328"))
                                                                                                                                                                  (stm_if ((stm_exp (exp_var "ж3820")))
                                                                                                                                                                          (stm_exp (exp_val (ty.enum Edoubleop) (CMP)))
                                                                                                                                                                          (stm_let "ga#329"
                                                                                                                                                                                   (ty.bool)
                                                                                                                                                                                   (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 10])))))
                                                                                                                                                                                   (stm_let "ж3819"
                                                                                                                                                                                            (ty.bool)
                                                                                                                                                                                            (stm_exp (exp_var "ga#329"))
                                                                                                                                                                                            (stm_if ((stm_exp (exp_var "ж3819")))
                                                                                                                                                                                                    (stm_exp (exp_val (ty.enum Edoubleop) (DADD)))
                                                                                                                                                                                                    (stm_let "ga#330"
                                                                                                                                                                                                             (ty.bool)
                                                                                                                                                                                                             (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 11])))))
                                                                                                                                                                                                             (stm_let "ж3818"
                                                                                                                                                                                                                      (ty.bool)
                                                                                                                                                                                                                      (stm_exp (exp_var "ga#330"))
                                                                                                                                                                                                                      (stm_if ((stm_exp (exp_var "ж3818")))
                                                                                                                                                                                                                              (stm_exp (exp_val (ty.enum Edoubleop) (BIT)))
                                                                                                                                                                                                                              (stm_let "ga#331"
                                                                                                                                                                                                                                       (ty.bool)
                                                                                                                                                                                                                                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 12])))))
                                                                                                                                                                                                                                       (stm_let "ж3817"
                                                                                                                                                                                                                                                (ty.bool)
                                                                                                                                                                                                                                                (stm_exp (exp_var "ga#331"))
                                                                                                                                                                                                                                                (stm_if ((stm_exp (exp_var "ж3817")))
                                                                                                                                                                                                                                                        (stm_exp (exp_val (ty.enum Edoubleop) (BIC)))
                                                                                                                                                                                                                                                        (stm_let "ga#332"
                                                                                                                                                                                                                                                                 (ty.bool)
                                                                                                                                                                                                                                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 13])))))
                                                                                                                                                                                                                                                                 (stm_let "ж3816"
                                                                                                                                                                                                                                                                          (ty.bool)
                                                                                                                                                                                                                                                                          (stm_exp (exp_var "ga#332"))
                                                                                                                                                                                                                                                                          (stm_if ((stm_exp (exp_var "ж3816")))
                                                                                                                                                                                                                                                                                  (stm_exp (exp_val (ty.enum Edoubleop) (BIS)))
                                                                                                                                                                                                                                                                                  (stm_let "ga#333"
                                                                                                                                                                                                                                                                                           (ty.bool)
                                                                                                                                                                                                                                                                                           (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 14])))))
                                                                                                                                                                                                                                                                                           (stm_let "ж3815"
                                                                                                                                                                                                                                                                                                    (ty.bool)
                                                                                                                                                                                                                                                                                                    (stm_exp (exp_var "ga#333"))
                                                                                                                                                                                                                                                                                                    (stm_if ((stm_exp (exp_var "ж3815")))
                                                                                                                                                                                                                                                                                                            (stm_exp (exp_val (ty.enum Edoubleop) (XOR)))
                                                                                                                                                                                                                                                                                                            (stm_let "ga#334"
                                                                                                                                                                                                                                                                                                                     (ty.bool)
                                                                                                                                                                                                                                                                                                                     (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 15])))))
                                                                                                                                                                                                                                                                                                                     (stm_let "ж3814"
                                                                                                                                                                                                                                                                                                                              (ty.bool)
                                                                                                                                                                                                                                                                                                                              (stm_exp (exp_var "ga#334"))
                                                                                                                                                                                                                                                                                                                              (stm_if ((stm_exp (exp_var "ж3814")))
                                                                                                                                                                                                                                                                                                                                      (stm_exp (exp_val (ty.enum Edoubleop) (AND)))
                                                                                                                                                                                                                                                                                                                                      (stm_seq (stm_assert (exp_false) (exp_string "Pattern match failure at unknown location"))
                                                                                                                                                                                                                                                                                                                                               (stm_fail _ "failure")))))))))))))))))))))))))))))))))))))).
    
    (*
      Extended type
        parameter arg#
          doubleop
        return value
          $0
    *)
    Definition fun_encdec_doubleop_forwards_matches : Stm [
                                                            "arg#"  ∷  ty.enum Edoubleop
                                                          ]
                                                          (ty.bool) :=
      stm_let "ж3826"
              (ty.enum Edoubleop)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Edoubleop
                              (stm_exp (exp_var "ж3826"))
                              (fun K => match K with
                                        | ADD  => stm_exp (exp_true)
                                        | ADDC => stm_exp (exp_true)
                                        | AND  => stm_exp (exp_true)
                                        | BIC  => stm_exp (exp_true)
                                        | BIS  => stm_exp (exp_true)
                                        | BIT  => stm_exp (exp_true)
                                        | CMP  => stm_exp (exp_true)
                                        | DADD => stm_exp (exp_true)
                                        | MOV  => stm_exp (exp_true)
                                        | SUB  => stm_exp (exp_true)
                                        | SUBC => stm_exp (exp_true)
                                        | XOR  => stm_exp (exp_true)
                                        end)).
    
    (*
      Extended type
        parameter arg#
          ?[51:4]
        return value
          $0
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_encdec_doubleop_backwards_matches : Stm [
                                                             "arg#"  ∷  ty.bvec (4)
                                                           ]
                                                           (ty.bool) :=
      stm_let "b__0"
              (ty.bvec (4))
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#336"
                       (ty.bool)
                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 4])))))
                       (stm_let "ж3851"
                                (ty.bool)
                                (stm_exp (exp_var "ga#336"))
                                (stm_if ((stm_exp (exp_var "ж3851")))
                                        (stm_exp (exp_true))
                                        (stm_let "ga#337"
                                                 (ty.bool)
                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 5])))))
                                                 (stm_let "ж3850"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#337"))
                                                          (stm_if ((stm_exp (exp_var "ж3850")))
                                                                  (stm_exp (exp_true))
                                                                  (stm_let "ga#338"
                                                                           (ty.bool)
                                                                           (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 6])))))
                                                                           (stm_let "ж3849"
                                                                                    (ty.bool)
                                                                                    (stm_exp (exp_var "ga#338"))
                                                                                    (stm_if ((stm_exp (exp_var "ж3849")))
                                                                                            (stm_exp (exp_true))
                                                                                            (stm_let "ga#339"
                                                                                                     (ty.bool)
                                                                                                     (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 7])))))
                                                                                                     (stm_let "ж3848"
                                                                                                              (ty.bool)
                                                                                                              (stm_exp (exp_var "ga#339"))
                                                                                                              (stm_if ((stm_exp (exp_var "ж3848")))
                                                                                                                      (stm_exp (exp_true))
                                                                                                                      (stm_let "ga#340"
                                                                                                                               (ty.bool)
                                                                                                                               (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 8])))))
                                                                                                                               (stm_let "ж3847"
                                                                                                                                        (ty.bool)
                                                                                                                                        (stm_exp (exp_var "ga#340"))
                                                                                                                                        (stm_if ((stm_exp (exp_var "ж3847")))
                                                                                                                                                (stm_exp (exp_true))
                                                                                                                                                (stm_let "ga#341"
                                                                                                                                                         (ty.bool)
                                                                                                                                                         (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 9])))))
                                                                                                                                                         (stm_let "ж3846"
                                                                                                                                                                  (ty.bool)
                                                                                                                                                                  (stm_exp (exp_var "ga#341"))
                                                                                                                                                                  (stm_if ((stm_exp (exp_var "ж3846")))
                                                                                                                                                                          (stm_exp (exp_true))
                                                                                                                                                                          (stm_let "ga#342"
                                                                                                                                                                                   (ty.bool)
                                                                                                                                                                                   (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 10])))))
                                                                                                                                                                                   (stm_let "ж3845"
                                                                                                                                                                                            (ty.bool)
                                                                                                                                                                                            (stm_exp (exp_var "ga#342"))
                                                                                                                                                                                            (stm_if ((stm_exp (exp_var "ж3845")))
                                                                                                                                                                                                    (stm_exp (exp_true))
                                                                                                                                                                                                    (stm_let "ga#343"
                                                                                                                                                                                                             (ty.bool)
                                                                                                                                                                                                             (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 11])))))
                                                                                                                                                                                                             (stm_let "ж3844"
                                                                                                                                                                                                                      (ty.bool)
                                                                                                                                                                                                                      (stm_exp (exp_var "ga#343"))
                                                                                                                                                                                                                      (stm_if ((stm_exp (exp_var "ж3844")))
                                                                                                                                                                                                                              (stm_exp (exp_true))
                                                                                                                                                                                                                              (stm_let "ga#344"
                                                                                                                                                                                                                                       (ty.bool)
                                                                                                                                                                                                                                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 12])))))
                                                                                                                                                                                                                                       (stm_let "ж3843"
                                                                                                                                                                                                                                                (ty.bool)
                                                                                                                                                                                                                                                (stm_exp (exp_var "ga#344"))
                                                                                                                                                                                                                                                (stm_if ((stm_exp (exp_var "ж3843")))
                                                                                                                                                                                                                                                        (stm_exp (exp_true))
                                                                                                                                                                                                                                                        (stm_let "ga#345"
                                                                                                                                                                                                                                                                 (ty.bool)
                                                                                                                                                                                                                                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 13])))))
                                                                                                                                                                                                                                                                 (stm_let "ж3842"
                                                                                                                                                                                                                                                                          (ty.bool)
                                                                                                                                                                                                                                                                          (stm_exp (exp_var "ga#345"))
                                                                                                                                                                                                                                                                          (stm_if ((stm_exp (exp_var "ж3842")))
                                                                                                                                                                                                                                                                                  (stm_exp (exp_true))
                                                                                                                                                                                                                                                                                  (stm_let "ga#346"
                                                                                                                                                                                                                                                                                           (ty.bool)
                                                                                                                                                                                                                                                                                           (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 14])))))
                                                                                                                                                                                                                                                                                           (stm_let "ж3841"
                                                                                                                                                                                                                                                                                                    (ty.bool)
                                                                                                                                                                                                                                                                                                    (stm_exp (exp_var "ga#346"))
                                                                                                                                                                                                                                                                                                    (stm_if ((stm_exp (exp_var "ж3841")))
                                                                                                                                                                                                                                                                                                            (stm_exp (exp_true))
                                                                                                                                                                                                                                                                                                            (stm_let "ga#347"
                                                                                                                                                                                                                                                                                                                     (ty.bool)
                                                                                                                                                                                                                                                                                                                     (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 4) ([bv 15])))))
                                                                                                                                                                                                                                                                                                                     (stm_let "ж3840"
                                                                                                                                                                                                                                                                                                                              (ty.bool)
                                                                                                                                                                                                                                                                                                                              (stm_exp (exp_var "ga#347"))
                                                                                                                                                                                                                                                                                                                              (stm_if ((stm_exp (exp_var "ж3840")))
                                                                                                                                                                                                                                                                                                                                      (stm_exp (exp_true))
                                                                                                                                                                                                                                                                                                                                      (stm_exp (exp_false)))))))))))))))))))))))))))))))))))))).
    
    (*
      Extended type
        An error occurred: (nanosail/NanosailToMicrosail/Types/ExtendedType.ml:267) number of parameters (parameter merge#var) is different from number of number of extended types (BW,AM,Register)
    *)
    Definition fun_rrc_inst : Stm [
                                    "merge#var"  ∷  ty.tuple [
                                                                 ty.enum Ebw;
                                                                 ty.enum Eam;
                                                                 ty.enum Eregister
                                                               ]
                                  ]
                                  (ty.unit).
      refine (
      stm_let "ж3852"
              (ty.tuple [
                          ty.enum Ebw;
                          ty.enum Eam;
                          ty.enum Eregister
                        ])
              (stm_exp (exp_var "merge#var"))
              (stm_match_tuple (stm_exp (exp_var "ж3852"))
                               (tuplepat_snoc (tuplepat_snoc (tuplepat_snoc (tuplepat_nil) "ж3917") "ж3916") "ж3915")
                               (stm_let "addressingMode"
                                        (ty.enum Eam)
                                        (stm_exp (exp_var "ж3916"))
                                        (stm_let "reg"
                                                 (ty.enum Eregister)
                                                 (stm_exp (exp_var "ж3917"))
                                                 (stm_match_enum Ebw
                                                                 (stm_exp (exp_var "ж3915"))
                                                                 (fun K => match K with
                                                                           | BYTE_INSTRUCTION => stm_let "ga#354"
                                                                                                         (ty.union Uwordbyte)
                                                                                                         (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                      (_::_)
                                                                                                                                                      ((exp_val (ty.enum Ebw) (BYTE_INSTRUCTION)))%exp)
                                                                                                                                            (_::_)
                                                                                                                                            ((exp_var "reg"))%exp)
                                                                                                                                  (_::_)
                                                                                                                                  ((exp_var "addressingMode"))%exp))
                                                                                                         (stm_let "ж3869"
                                                                                                                  (ty.union Uwordbyte)
                                                                                                                  (stm_exp (exp_var "ga#354"))
                                                                                                                  (stm_match_union_alt_list Uwordbyte
                                                                                                                                            (stm_exp (exp_var "ж3869"))
                                                                                                                                            [
                                                                                                                                              existT Kbyte (MkAlt (pat_var "ж3882") (stm_fail _ "failure"));
                                                                                                                                              existT Kword (MkAlt (pat_var "value") (stm_let "shift"
                                                                                                                                                                                             (ty.bvec (7))
                                                                                                                                                                                             (stm_exp (exp_unop (uop.vector_subrange 1 7) (exp_var "value")))
                                                                                                                                                                                             (stm_let "carry"
                                                                                                                                                                                                      (ty.bvec (1))
                                                                                                                                                                                                      (stm_call getCarryBit (env.snoc (env.nil)
                                                                                                                                                                                                                                      (_::_)
                                                                                                                                                                                                                                      ((exp_val (ty.unit) (tt)))%exp))
                                                                                                                                                                                                      (stm_seq (stm_let "ga#355"
                                                                                                                                                                                                                        (ty.bvec (1))
                                                                                                                                                                                                                        (stm_exp (exp_unop (uop.vector_subrange 0 1) (exp_var "value")))
                                                                                                                                                                                                                        (stm_call setCarrybitBit (env.snoc (env.nil)
                                                                                                                                                                                                                                                           (_::_)
                                                                                                                                                                                                                                                           ((exp_var "ga#355"))%exp)))
                                                                                                                                                                                                               (stm_let "res"
                                                                                                                                                                                                                        (ty.union Uwordbyte)
                                                                                                                                                                                                                        (stm_let "ga#359"
                                                                                                                                                                                                                                 (ty.bvec (8))
                                                                                                                                                                                                                                 (stm_exp (exp_binop (@bop.bvapp _ 1 7) (exp_var "carry") (exp_var "shift")))
                                                                                                                                                                                                                                 (stm_exp (exp_union Uwordbyte Kbyte (exp_var "ga#359"))))
                                                                                                                                                                                                                        (stm_seq (stm_call setResultStatusRegisters (env.snoc (env.nil)
                                                                                                                                                                                                                                                                              (_::_)
                                                                                                                                                                                                                                                                              ((exp_var "res"))%exp))
                                                                                                                                                                                                                                 (stm_seq (stm_call clearOverflowbit (env.snoc (env.nil)
                                                                                                                                                                                                                                                                               (_::_)
                                                                                                                                                                                                                                                                               ((exp_val (ty.unit) (tt)))%exp))
                                                                                                                                                                                                                                          (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                                                                                                                  (_::_)
                                                                                                                                                                                                                                                                                                  ((exp_val (ty.enum Ebw) (BYTE_INSTRUCTION)))%exp)
                                                                                                                                                                                                                                                                                        (_::_)
                                                                                                                                                                                                                                                                                        ((exp_var "reg"))%exp)
                                                                                                                                                                                                                                                                              (_::_)
                                                                                                                                                                                                                                                                              ((exp_var "addressingMode"))%exp)
                                                                                                                                                                                                                                                                    (_::_)
                                                                                                                                                                                                                                                                    ((exp_var "res"))%exp)))))))))
                                                                                                                                            ]
                                                                                                                                            Logic.I))
                                                                           | WORD_INSTRUCTION => stm_let "ga#348"
                                                                                                         (ty.union Uwordbyte)
                                                                                                         (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                      (_::_)
                                                                                                                                                      ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                                                                                                            (_::_)
                                                                                                                                            ((exp_var "reg"))%exp)
                                                                                                                                  (_::_)
                                                                                                                                  ((exp_var "addressingMode"))%exp))
                                                                                                         (stm_let "ж3853"
                                                                                                                  (ty.union Uwordbyte)
                                                                                                                  (stm_exp (exp_var "ga#348"))
                                                                                                                  (stm_match_union_alt_list Uwordbyte
                                                                                                                                            (stm_exp (exp_var "ж3853"))
                                                                                                                                            [
                                                                                                                                              existT Kbyte (MkAlt (pat_var "ж3866") (stm_fail _ "failure"));
                                                                                                                                              existT Kword (MkAlt (pat_var "value") (stm_let "shift"
                                                                                                                                                                                             (ty.bvec (15))
                                                                                                                                                                                             (stm_exp (exp_unop (uop.vector_subrange 1 15) (exp_var "value")))
                                                                                                                                                                                             (stm_let "carry"
                                                                                                                                                                                                      (ty.bvec (1))
                                                                                                                                                                                                      (stm_call getCarryBit (env.snoc (env.nil)
                                                                                                                                                                                                                                      (_::_)
                                                                                                                                                                                                                                      ((exp_val (ty.unit) (tt)))%exp))
                                                                                                                                                                                                      (stm_seq (stm_let "ga#349"
                                                                                                                                                                                                                        (ty.bvec (1))
                                                                                                                                                                                                                        (stm_exp (exp_unop (uop.vector_subrange 0 1) (exp_var "value")))
                                                                                                                                                                                                                        (stm_call setCarrybitBit (env.snoc (env.nil)
                                                                                                                                                                                                                                                           (_::_)
                                                                                                                                                                                                                                                           ((exp_var "ga#349"))%exp)))
                                                                                                                                                                                                               (stm_let "res"
                                                                                                                                                                                                                        (ty.union Uwordbyte)
                                                                                                                                                                                                                        (stm_let "ga#353"
                                                                                                                                                                                                                                 (ty.bvec (16))
                                                                                                                                                                                                                                 (stm_exp (exp_binop (@bop.bvapp _ 1 15) (exp_var "carry") (exp_var "shift")))
                                                                                                                                                                                                                                 (stm_exp (exp_union Uwordbyte Kword (exp_var "ga#353"))))
                                                                                                                                                                                                                        (stm_seq (stm_call setResultStatusRegisters (env.snoc (env.nil)
                                                                                                                                                                                                                                                                              (_::_)
                                                                                                                                                                                                                                                                              ((exp_var "res"))%exp))
                                                                                                                                                                                                                                 (stm_seq (stm_call clearOverflowbit (env.snoc (env.nil)
                                                                                                                                                                                                                                                                               (_::_)
                                                                                                                                                                                                                                                                               ((exp_val (ty.unit) (tt)))%exp))
                                                                                                                                                                                                                                          (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                                                                                                                  (_::_)
                                                                                                                                                                                                                                                                                                  ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                                                                                                                                                                                                                                                        (_::_)
                                                                                                                                                                                                                                                                                        ((exp_var "reg"))%exp)
                                                                                                                                                                                                                                                                              (_::_)
                                                                                                                                                                                                                                                                              ((exp_var "addressingMode"))%exp)
                                                                                                                                                                                                                                                                    (_::_)
                                                                                                                                                                                                                                                                    ((exp_var "res"))%exp)))))))))
                                                                                                                                            ]
                                                                                                                                            Logic.I))
                                                                           end)))))).
      all: try typeclasses eauto.
      all: try easy.
      (* STEVE: Some type errors!?  *)
    Restart.
      refine (stm_fail _ "").
    Defined.


    (*
      Extended type
        parameter bw
          BW
        parameter am
          AM
        parameter reg
          Register
        return value
          unit
    *)
    Definition fun_rra_inst : Stm [
                                    "bw"  ∷  ty.enum Ebw;
                                    "am"  ∷  ty.enum Eam;
                                    "reg"  ∷  ty.enum Eregister
                                  ]
                                  (ty.unit) :=
      stm_let "ga#360"
              (ty.union Uwordbyte)
              (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                           (_::_)
                                                           ((exp_var "bw"))%exp)
                                                 (_::_)
                                                 ((exp_var "reg"))%exp)
                                       (_::_)
                                       ((exp_var "am"))%exp))
              (stm_let "ж3918"
                       (ty.union Uwordbyte)
                       (stm_exp (exp_var "ga#360"))
                       (stm_match_union_alt_list Uwordbyte
                                                 (stm_exp (exp_var "ж3918"))
                                                 [
                                                   existT Kbyte (MkAlt (pat_var "ж3938") (stm_fail _ "failure"));
                                                   existT Kword (MkAlt (pat_var "value") (stm_let "res"
                                                                                                  (ty.union Uwordbyte)
                                                                                                  (stm_let "ж3919"
                                                                                                           (ty.enum Ebw)
                                                                                                           (stm_exp (exp_var "bw"))
                                                                                                           (stm_match_enum Ebw
                                                                                                                           (stm_exp (exp_var "ж3919"))
                                                                                                                           (fun K => match K with
                                                                                                                                     | BYTE_INSTRUCTION => stm_let "shift"
                                                                                                                                                                   (ty.bvec (7))
                                                                                                                                                                   (stm_exp (exp_unop (uop.vector_subrange 1 7) (exp_var "value")))
                                                                                                                                                                   (stm_seq (stm_let "ga#366"
                                                                                                                                                                                     (ty.bvec (1))
                                                                                                                                                                                     (stm_exp (exp_unop (uop.vector_subrange 0 1) (exp_var "value")))
                                                                                                                                                                                     (stm_call setCarrybitBit (env.snoc (env.nil)
                                                                                                                                                                                                                        (_::_)
                                                                                                                                                                                                                        ((exp_var "ga#366"))%exp)))
                                                                                                                                                                            (stm_let "b"
                                                                                                                                                                                     (ty.bvec (1))
                                                                                                                                                                                     (stm_exp (exp_unop (uop.vector_subrange 7 1) (exp_var "value")))
                                                                                                                                                                                     (stm_let "ga#368"
                                                                                                                                                                                              (ty.bvec (8))
                                                                                                                                                                                              (stm_exp (exp_binop (@bop.bvapp _ 1 7) (exp_var "b") (exp_var "shift")))
                                                                                                                                                                                              (stm_exp (exp_union Uwordbyte Kbyte (exp_var "ga#368"))))))
                                                                                                                                     | WORD_INSTRUCTION => stm_let "shift"
                                                                                                                                                                   (ty.bvec (15))
                                                                                                                                                                   (stm_exp (exp_unop (uop.vector_subrange 1 15) (exp_var "value")))
                                                                                                                                                                   (stm_seq (stm_let "ga#363"
                                                                                                                                                                                     (ty.bvec (1))
                                                                                                                                                                                     (stm_exp (exp_unop (uop.vector_subrange 0 1) (exp_var "value")))
                                                                                                                                                                                     (stm_call setCarrybitBit (env.snoc (env.nil)
                                                                                                                                                                                                                        (_::_)
                                                                                                                                                                                                                        ((exp_var "ga#363"))%exp)))
                                                                                                                                                                            (stm_let "b"
                                                                                                                                                                                     (ty.bvec (1))
                                                                                                                                                                                     (stm_exp (exp_unop (uop.vector_subrange 15 1) (exp_var "value")))
                                                                                                                                                                                     (stm_let "ga#365"
                                                                                                                                                                                              (ty.bvec (16))
                                                                                                                                                                                              (stm_exp (exp_binop (@bop.bvapp _ 1 15) (exp_var "b") (exp_var "shift")))
                                                                                                                                                                                              (stm_exp (exp_union Uwordbyte Kword (exp_var "ga#365"))))))
                                                                                                                                     end)))
                                                                                                  (stm_seq (stm_call setResultStatusRegisters (env.snoc (env.nil)
                                                                                                                                                        (_::_)
                                                                                                                                                        ((exp_var "res"))%exp))
                                                                                                           (stm_seq (stm_call clearOverflowbit (env.snoc (env.nil)
                                                                                                                                                         (_::_)
                                                                                                                                                         ((exp_val (ty.unit) (tt)))%exp))
                                                                                                                    (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                            (_::_)
                                                                                                                                                                            ((exp_var "bw"))%exp)
                                                                                                                                                                  (_::_)
                                                                                                                                                                  ((exp_var "reg"))%exp)
                                                                                                                                                        (_::_)
                                                                                                                                                        ((exp_var "am"))%exp)
                                                                                                                                              (_::_)
                                                                                                                                              ((exp_var "res"))%exp))))))
                                                 ]
                                                 Logic.I)).
    
    (*
      Extended type
        parameter bw
          BW
        parameter addressingMode
          AM
        parameter reg
          Register
        return value
          unit
    *)
    Definition fun_push_inst : Stm [
                                     "bw"  ∷  ty.enum Ebw;
                                     "addressingMode"  ∷  ty.enum Eam;
                                     "reg"  ∷  ty.enum Eregister
                                   ]
                                   (ty.unit) :=
      stm_let "sourceValue"
              (ty.union Uwordbyte)
              (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                           (_::_)
                                                           ((exp_var "bw"))%exp)
                                                 (_::_)
                                                 ((exp_var "reg"))%exp)
                                       (_::_)
                                       ((exp_var "addressingMode"))%exp))
              (stm_seq (stm_seq (stm_let "ж3941"
                                         (ty.wordBits)
                                         (stm_let "ga#370"
                                                  (ty.bvec (16))
                                                  (stm_let "ga#369"
                                                           (ty.bvec (4))
                                                           (stm_call neg_vec4 (env.snoc (env.nil)
                                                                                        (_::_)
                                                                                        ((exp_val (ty.bvec 4) ([bv 2])))%exp))
                                                           (stm_exp (exp_unop (uop.sext (n := 16)) (exp_var "ga#369"))))
                                                  (stm_let "жreg_SP_reg_3942"
                                                           (ty.wordBits)
                                                           (stm_read_register SP_reg)
                                                           (stm_exp (exp_binop bop.bvadd (exp_var "жreg_SP_reg_3942") (exp_var "ga#370")))))
                                         (stm_write_register SP_reg (exp_var "ж3941")))
                                (stm_exp (exp_val (ty.unit) (tt))))
                       (stm_let "жreg_SP_reg_3944"
                                (ty.wordBits)
                                (stm_read_register SP_reg)
                                (stm_call writeMemInstruction (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                            (_::_)
                                                                                            ((exp_var "bw"))%exp)
                                                                                  (_::_)
                                                                                  ((exp_var "жreg_SP_reg_3944"))%exp)
                                                                        (_::_)
                                                                        ((exp_var "sourceValue"))%exp)))).
    
    (*
      Extended type
        parameter _ж3947
          BW
        parameter addressingMode
          AM
        parameter reg
          Register
        return value
          unit
    *)
    Definition fun_swpb_inst : Stm [
                                     "_ж3947"  ∷  ty.enum Ebw;
                                     "addressingMode"  ∷  ty.enum Eam;
                                     "reg"  ∷  ty.enum Eregister
                                   ]
                                   (ty.unit) :=
      stm_let "ga#372"
              (ty.union Uwordbyte)
              (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                           (_::_)
                                                           ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                 (_::_)
                                                 ((exp_var "reg"))%exp)
                                       (_::_)
                                       ((exp_var "addressingMode"))%exp))
              (stm_let "ж3948"
                       (ty.union Uwordbyte)
                       (stm_exp (exp_var "ga#372"))
                       (stm_match_union_alt_list Uwordbyte
                                                 (stm_exp (exp_var "ж3948"))
                                                 [
                                                   existT Kbyte (MkAlt (pat_var "ж3952") (stm_fail _ "failure"));
                                                   existT Kword (MkAlt (pat_var "value") (stm_let "a"
                                                                                                  (ty.bvec (8))
                                                                                                  (stm_exp (exp_unop (uop.vector_subrange 0 8) (exp_var "value")))
                                                                                                  (stm_let "b"
                                                                                                           (ty.bvec (8))
                                                                                                           (stm_exp (exp_unop (uop.vector_subrange 8 8) (exp_var "value")))
                                                                                                           (stm_let "res"
                                                                                                                    (ty.union Uwordbyte)
                                                                                                                    (stm_let "ga#373"
                                                                                                                             (ty.bvec (16))
                                                                                                                             (stm_exp (exp_binop (@bop.bvapp _ 8 8) (exp_var "a") (exp_var "b")))
                                                                                                                             (stm_exp (exp_union Uwordbyte Kword (exp_var "ga#373"))))
                                                                                                                    (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                            (_::_)
                                                                                                                                                                            ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                                                                                                                                  (_::_)
                                                                                                                                                                  ((exp_var "reg"))%exp)
                                                                                                                                                        (_::_)
                                                                                                                                                        ((exp_var "addressingMode"))%exp)
                                                                                                                                              (_::_)
                                                                                                                                              ((exp_var "res"))%exp))))))
                                                 ]
                                                 Logic.I)).
    
    (*
      Extended type
        An error occurred: (nanosail/NanosailToMicrosail/Types/ExtendedType.ml:267) number of parameters (parameter merge#var) is different from number of number of extended types (BW,AM,Register)
    *)
    Definition fun_call_inst : Stm [
                                     "merge#var"  ∷  ty.tuple [
                                                                  ty.enum Ebw;
                                                                  ty.enum Eam;
                                                                  ty.enum Eregister
                                                                ]
                                   ]
                                   (ty.unit).
      refine (stm_let "ж3955"
              (ty.tuple [
                          ty.enum Ebw;
                          ty.enum Eam;
                          ty.enum Eregister
                        ])
              (stm_exp (exp_var "merge#var"))
              (stm_match_tuple (stm_exp (exp_var "ж3955"))
                               (tuplepat_snoc (tuplepat_snoc (tuplepat_snoc (tuplepat_nil) "ж3997") "ж3996") "ж3995")
                               (stm_let "addressingMode"
                                        (ty.enum Eam)
                                        (stm_exp (exp_var "ж3996"))
                                        (stm_let "reg"
                                                 (ty.enum Eregister)
                                                 (stm_exp (exp_var "ж3997"))
                                                 (stm_match_enum Ebw
                                                                 (stm_exp (exp_var "ж3995"))
                                                                 (fun K => match K with
                                                                           | BYTE_INSTRUCTION => stm_seq (stm_exp (exp_union Uexception Knotallowed (exp_string "There is no byte version of the call instruction")))
                                                                                                         (stm_fail _ "failure")
                                                                           | WORD_INSTRUCTION => stm_let "dst"
                                                                                                         (ty.union Uwordbyte)
                                                                                                         (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                      (_::_)
                                                                                                                                                      ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                                                                                                            (_::_)
                                                                                                                                            ((exp_var "reg"))%exp)
                                                                                                                                  (_::_)
                                                                                                                                  ((exp_var "addressingMode"))%exp))
                                                                                                         (stm_seq (stm_seq (stm_let "ж3956"
                                                                                                                                    (ty.wordBits)
                                                                                                                                    (stm_let "ga#375"
                                                                                                                                             (ty.bvec (16))
                                                                                                                                             (stm_let "ga#374"
                                                                                                                                                      (ty.bvec (4))
                                                                                                                                                      (stm_call neg_vec4 (env.snoc (env.nil)
                                                                                                                                                                                   (_::_)
                                                                                                                                                                                   ((exp_val (ty.bvec 4) ([bv 2])))%exp))
                                                                                                                                                      (stm_exp (exp_unop (uop.sext (n := 16)) (exp_var "ga#374"))))
                                                                                                                                             (stm_let "жreg_SP_reg_3957"
                                                                                                                                                      (ty.wordBits)
                                                                                                                                                      (stm_read_register SP_reg)
                                                                                                                                                      (stm_exp (exp_binop bop.bvadd (exp_var "жreg_SP_reg_3957") (exp_var "ga#375")))))
                                                                                                                                    (stm_write_register SP_reg (exp_var "ж3956")))
                                                                                                                           (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                  (stm_seq (stm_let "PCValue"
                                                                                                                                    (ty.union Uwordbyte)
                                                                                                                                    (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                 (_::_)
                                                                                                                                                                                 ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                                                                                                                                       (_::_)
                                                                                                                                                                       ((exp_val (ty.enum Eregister) (PC)))%exp)
                                                                                                                                                             (_::_)
                                                                                                                                                             ((exp_val (ty.enum Eam) (REGISTER_MODE)))%exp))
                                                                                                                                    (stm_let "жreg_SP_reg_3959"
                                                                                                                                             (ty.wordBits)
                                                                                                                                             (stm_read_register SP_reg)
                                                                                                                                             (stm_call writeMemInstruction (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                         (_::_)
                                                                                                                                                                                                         ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                                                                                                                                                               (_::_)
                                                                                                                                                                                               ((exp_var "жreg_SP_reg_3959"))%exp)
                                                                                                                                                                                     (_::_)
                                                                                                                                                                                     ((exp_var "PCValue"))%exp))))
                                                                                                                           (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                   (_::_)
                                                                                                                                                                                   ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                                                                                                                                         (_::_)
                                                                                                                                                                         ((exp_var "reg"))%exp)
                                                                                                                                                               (_::_)
                                                                                                                                                               ((exp_val (ty.enum Eam) (REGISTER_MODE)))%exp)
                                                                                                                                                     (_::_)
                                                                                                                                                     ((exp_var "dst"))%exp))))
                                                                           end)))))).
      all: try typeclasses eauto.
      all: try easy.
    Restart.
      refine (stm_fail _ "").
    Defined.

    (*
      Extended type
        parameter _ж3998
          BW
        parameter _ж3999
          AM
        parameter _ж4000
          Register
        return value
          unit
    *)
    Definition fun_reti_inst : Stm [
                                     "_ж3998"  ∷  ty.enum Ebw;
                                     "_ж3999"  ∷  ty.enum Eam;
                                     "_ж4000"  ∷  ty.enum Eregister
                                   ]
                                   (ty.unit) :=
      stm_seq (stm_let "tos"
                       (ty.union Uwordbyte)
                       (stm_let "жreg_SP_reg_4001"
                                (ty.wordBits)
                                (stm_read_register SP_reg)
                                (stm_call readMem (env.snoc (env.snoc (env.nil)
                                                                      (_::_)
                                                                      ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                            (_::_)
                                                            ((exp_var "жreg_SP_reg_4001"))%exp)))
                       (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                               (_::_)
                                                                               ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                                     (_::_)
                                                                     ((exp_val (ty.enum Eregister) (SRCG1)))%exp)
                                                           (_::_)
                                                           ((exp_val (ty.enum Eam) (REGISTER_MODE)))%exp)
                                                 (_::_)
                                                 ((exp_var "tos"))%exp)))
              (stm_seq (stm_seq (stm_let "ж4003"
                                         (ty.wordBits)
                                         (stm_let "ga#380"
                                                  (ty.bvec (16))
                                                  (stm_exp (exp_unop (uop.zext (n := 16)) (exp_val (ty.bvec 4) ([bv 2]))))
                                                  (stm_let "жreg_SP_reg_4004"
                                                           (ty.wordBits)
                                                           (stm_read_register SP_reg)
                                                           (stm_exp (exp_binop bop.bvadd (exp_var "жreg_SP_reg_4004") (exp_var "ga#380")))))
                                         (stm_write_register SP_reg (exp_var "ж4003")))
                                (stm_exp (exp_val (ty.unit) (tt))))
                       (stm_seq (stm_let "tos"
                                         (ty.union Uwordbyte)
                                         (stm_let "жreg_SP_reg_4006"
                                                  (ty.wordBits)
                                                  (stm_read_register SP_reg)
                                                  (stm_call readMem (env.snoc (env.snoc (env.nil)
                                                                                        (_::_)
                                                                                        ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                                              (_::_)
                                                                              ((exp_var "жreg_SP_reg_4006"))%exp)))
                                         (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                 (_::_)
                                                                                                 ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                                                       (_::_)
                                                                                       ((exp_val (ty.enum Eregister) (PC)))%exp)
                                                                             (_::_)
                                                                             ((exp_val (ty.enum Eam) (REGISTER_MODE)))%exp)
                                                                   (_::_)
                                                                   ((exp_var "tos"))%exp)))
                                (stm_seq (stm_let "ж4008"
                                                  (ty.wordBits)
                                                  (stm_let "ga#383"
                                                           (ty.bvec (16))
                                                           (stm_exp (exp_unop (uop.zext (n := 16)) (exp_val (ty.bvec 4) ([bv 2]))))
                                                           (stm_let "жreg_SP_reg_4009"
                                                                    (ty.wordBits)
                                                                    (stm_read_register SP_reg)
                                                                    (stm_exp (exp_binop bop.bvadd (exp_var "жreg_SP_reg_4009") (exp_var "ga#383")))))
                                                  (stm_write_register SP_reg (exp_var "ж4008")))
                                         (stm_exp (exp_val (ty.unit) (tt)))))).
    
    (*
      Extended type
        parameter _ж4016
          BW
        parameter addressingMode
          AM
        parameter reg
          Register
        return value
          unit
    *)
    Definition fun_sxt_inst : Stm [
                                    "_ж4016"  ∷  ty.enum Ebw;
                                    "addressingMode"  ∷  ty.enum Eam;
                                    "reg"  ∷  ty.enum Eregister
                                  ]
                                  (ty.unit) :=
      stm_seq (stm_call clearStatusRegisters (env.snoc (env.nil)
                                                       (_::_)
                                                       ((exp_val (ty.unit) (tt)))%exp))
              (stm_let "ga#385"
                       (ty.union Uwordbyte)
                       (stm_call read (env.snoc (env.snoc (env.snoc (env.nil)
                                                                    (_::_)
                                                                    ((exp_val (ty.enum Ebw) (BYTE_INSTRUCTION)))%exp)
                                                          (_::_)
                                                          ((exp_var "reg"))%exp)
                                                (_::_)
                                                ((exp_var "addressingMode"))%exp))
                       (stm_let "ж4018"
                                (ty.union Uwordbyte)
                                (stm_exp (exp_var "ga#385"))
                                (stm_match_union_alt_list Uwordbyte
                                                          (stm_exp (exp_var "ж4018"))
                                                          [
                                                            existT Kbyte (MkAlt (pat_var "value") (stm_let "res"
                                                                                                           (ty.union Uwordbyte)
                                                                                                           (stm_let "ga#393"
                                                                                                                    (ty.bvec (16))
                                                                                                                    (stm_exp (exp_unop (uop.sext (n := 16)) (exp_var "value")))
                                                                                                                    (stm_exp (exp_union Uwordbyte Kword (exp_var "ga#393"))))
                                                                                                           (stm_seq (stm_let "ga#386"
                                                                                                                             (ty.bool)
                                                                                                                             (stm_call isNegative (env.snoc (env.nil)
                                                                                                                                                            (_::_)
                                                                                                                                                            ((exp_var "res"))%exp))
                                                                                                                             (stm_let "ж4019"
                                                                                                                                      (ty.bool)
                                                                                                                                      (stm_exp (exp_var "ga#386"))
                                                                                                                                      (stm_if ((stm_exp (exp_var "ж4019")))
                                                                                                                                              (stm_call setNegativebitTrue (env.snoc (env.nil)
                                                                                                                                                                                     (_::_)
                                                                                                                                                                                     ((exp_val (ty.unit) (tt)))%exp))
                                                                                                                                              (stm_exp (exp_val (ty.unit) (tt))))))
                                                                                                                    (stm_seq (stm_let "ga#388"
                                                                                                                                      (ty.bool)
                                                                                                                                      (stm_call isZero (env.snoc (env.nil)
                                                                                                                                                                 (_::_)
                                                                                                                                                                 ((exp_var "res"))%exp))
                                                                                                                                      (stm_let "ж4021"
                                                                                                                                               (ty.bool)
                                                                                                                                               (stm_exp (exp_var "ga#388"))
                                                                                                                                               (stm_if ((stm_exp (exp_var "ж4021")))
                                                                                                                                                       (stm_call setZerobitTrue (env.snoc (env.nil)
                                                                                                                                                                                          (_::_)
                                                                                                                                                                                          ((exp_val (ty.unit) (tt)))%exp))
                                                                                                                                                       (stm_exp (exp_val (ty.unit) (tt))))))
                                                                                                                             (stm_seq (stm_let "ga#391"
                                                                                                                                               (ty.bool)
                                                                                                                                               (stm_let "ga#390"
                                                                                                                                                        (ty.bool)
                                                                                                                                                        (stm_call isZero (env.snoc (env.nil)
                                                                                                                                                                                   (_::_)
                                                                                                                                                                                   ((exp_var "res"))%exp))
                                                                                                                                                        (stm_exp (exp_unop uop.not (exp_var "ga#390"))))
                                                                                                                                               (stm_let "ж4023"
                                                                                                                                                        (ty.bool)
                                                                                                                                                        (stm_exp (exp_var "ga#391"))
                                                                                                                                                        (stm_if ((stm_exp (exp_var "ж4023")))
                                                                                                                                                                (stm_call setCarrybitTrue (env.snoc (env.nil)
                                                                                                                                                                                                    (_::_)
                                                                                                                                                                                                    ((exp_val (ty.unit) (tt)))%exp))
                                                                                                                                                                (stm_exp (exp_val (ty.unit) (tt))))))
                                                                                                                                      (stm_call write (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                              (_::_)
                                                                                                                                                                                              ((exp_val (ty.enum Ebw) (WORD_INSTRUCTION)))%exp)
                                                                                                                                                                                    (_::_)
                                                                                                                                                                                    ((exp_var "reg"))%exp)
                                                                                                                                                                          (_::_)
                                                                                                                                                                          ((exp_var "addressingMode"))%exp)
                                                                                                                                                                (_::_)
                                                                                                                                                                ((exp_var "res"))%exp)))))));
                                                            existT Kword (MkAlt (pat_var "ж4036") (stm_fail _ "failure"))
                                                          ]
                                                          Logic.I))).
    
    (*
      Extended type
        parameter arg#
          singleop
        return value
          ?[52]
      
      [0] : Sail type: bitvector(9)
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_encdec_singleop_forwards : Stm [
                                                    "arg#"  ∷  ty.enum Esingleop
                                                  ]
                                                  (ty.bvec (9)) :=
      stm_let "ж4039"
              (ty.enum Esingleop)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Esingleop
                              (stm_exp (exp_var "ж4039"))
                              (fun K => match K with
                                        | CALL => stm_exp (exp_val (ty.bvec 9) ([bv 37]))
                                        | PUSH => stm_exp (exp_val (ty.bvec 9) ([bv 36]))
                                        | RETI => stm_exp (exp_val (ty.bvec 9) ([bv 38]))
                                        | RRA  => stm_exp (exp_val (ty.bvec 9) ([bv 34]))
                                        | RRC  => stm_exp (exp_val (ty.bvec 9) ([bv 32]))
                                        | SWPB => stm_exp (exp_val (ty.bvec 9) ([bv 33]))
                                        | SXT  => stm_exp (exp_val (ty.bvec 9) ([bv 35]))
                                        end)).
    
    (*
      Extended type
        parameter arg#
          ?[53:9]
        return value
          singleop
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_encdec_singleop_backwards : Stm [
                                                     "arg#"  ∷  ty.bvec (9)
                                                   ]
                                                   (ty.enum Esingleop) :=
      stm_let "b__0"
              (ty.bvec (9))
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#394"
                       (ty.bool)
                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 9) ([bv 32])))))
                       (stm_let "ж4057"
                                (ty.bool)
                                (stm_exp (exp_var "ga#394"))
                                (stm_if ((stm_exp (exp_var "ж4057")))
                                        (stm_exp (exp_val (ty.enum Esingleop) (RRC)))
                                        (stm_let "ga#395"
                                                 (ty.bool)
                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 9) ([bv 34])))))
                                                 (stm_let "ж4056"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#395"))
                                                          (stm_if ((stm_exp (exp_var "ж4056")))
                                                                  (stm_exp (exp_val (ty.enum Esingleop) (RRA)))
                                                                  (stm_let "ga#396"
                                                                           (ty.bool)
                                                                           (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 9) ([bv 36])))))
                                                                           (stm_let "ж4055"
                                                                                    (ty.bool)
                                                                                    (stm_exp (exp_var "ga#396"))
                                                                                    (stm_if ((stm_exp (exp_var "ж4055")))
                                                                                            (stm_exp (exp_val (ty.enum Esingleop) (PUSH)))
                                                                                            (stm_let "ga#397"
                                                                                                     (ty.bool)
                                                                                                     (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 9) ([bv 33])))))
                                                                                                     (stm_let "ж4054"
                                                                                                              (ty.bool)
                                                                                                              (stm_exp (exp_var "ga#397"))
                                                                                                              (stm_if ((stm_exp (exp_var "ж4054")))
                                                                                                                      (stm_exp (exp_val (ty.enum Esingleop) (SWPB)))
                                                                                                                      (stm_let "ga#398"
                                                                                                                               (ty.bool)
                                                                                                                               (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 9) ([bv 37])))))
                                                                                                                               (stm_let "ж4053"
                                                                                                                                        (ty.bool)
                                                                                                                                        (stm_exp (exp_var "ga#398"))
                                                                                                                                        (stm_if ((stm_exp (exp_var "ж4053")))
                                                                                                                                                (stm_exp (exp_val (ty.enum Esingleop) (CALL)))
                                                                                                                                                (stm_let "ga#399"
                                                                                                                                                         (ty.bool)
                                                                                                                                                         (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 9) ([bv 38])))))
                                                                                                                                                         (stm_let "ж4052"
                                                                                                                                                                  (ty.bool)
                                                                                                                                                                  (stm_exp (exp_var "ga#399"))
                                                                                                                                                                  (stm_if ((stm_exp (exp_var "ж4052")))
                                                                                                                                                                          (stm_exp (exp_val (ty.enum Esingleop) (RETI)))
                                                                                                                                                                          (stm_let "ga#400"
                                                                                                                                                                                   (ty.bool)
                                                                                                                                                                                   (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 9) ([bv 35])))))
                                                                                                                                                                                   (stm_let "ж4051"
                                                                                                                                                                                            (ty.bool)
                                                                                                                                                                                            (stm_exp (exp_var "ga#400"))
                                                                                                                                                                                            (stm_if ((stm_exp (exp_var "ж4051")))
                                                                                                                                                                                                    (stm_exp (exp_val (ty.enum Esingleop) (SXT)))
                                                                                                                                                                                                    (stm_seq (stm_assert (exp_false) (exp_string "Pattern match failure at unknown location"))
                                                                                                                                                                                                             (stm_fail _ "failure"))))))))))))))))))))))).
    
    (*
      Extended type
        parameter arg#
          singleop
        return value
          $0
    *)
    Definition fun_encdec_singleop_forwards_matches : Stm [
                                                            "arg#"  ∷  ty.enum Esingleop
                                                          ]
                                                          (ty.bool) :=
      stm_let "ж4058"
              (ty.enum Esingleop)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Esingleop
                              (stm_exp (exp_var "ж4058"))
                              (fun K => match K with
                                        | CALL => stm_exp (exp_true)
                                        | PUSH => stm_exp (exp_true)
                                        | RETI => stm_exp (exp_true)
                                        | RRA  => stm_exp (exp_true)
                                        | RRC  => stm_exp (exp_true)
                                        | SWPB => stm_exp (exp_true)
                                        | SXT  => stm_exp (exp_true)
                                        end)).
    
    (*
      Extended type
        parameter arg#
          ?[54:9]
        return value
          $0
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_encdec_singleop_backwards_matches : Stm [
                                                             "arg#"  ∷  ty.bvec (9)
                                                           ]
                                                           (ty.bool) :=
      stm_let "b__0"
              (ty.bvec (9))
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#402"
                       (ty.bool)
                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 9) ([bv 32])))))
                       (stm_let "ж4073"
                                (ty.bool)
                                (stm_exp (exp_var "ga#402"))
                                (stm_if ((stm_exp (exp_var "ж4073")))
                                        (stm_exp (exp_true))
                                        (stm_let "ga#403"
                                                 (ty.bool)
                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 9) ([bv 34])))))
                                                 (stm_let "ж4072"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#403"))
                                                          (stm_if ((stm_exp (exp_var "ж4072")))
                                                                  (stm_exp (exp_true))
                                                                  (stm_let "ga#404"
                                                                           (ty.bool)
                                                                           (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 9) ([bv 36])))))
                                                                           (stm_let "ж4071"
                                                                                    (ty.bool)
                                                                                    (stm_exp (exp_var "ga#404"))
                                                                                    (stm_if ((stm_exp (exp_var "ж4071")))
                                                                                            (stm_exp (exp_true))
                                                                                            (stm_let "ga#405"
                                                                                                     (ty.bool)
                                                                                                     (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 9) ([bv 33])))))
                                                                                                     (stm_let "ж4070"
                                                                                                              (ty.bool)
                                                                                                              (stm_exp (exp_var "ga#405"))
                                                                                                              (stm_if ((stm_exp (exp_var "ж4070")))
                                                                                                                      (stm_exp (exp_true))
                                                                                                                      (stm_let "ga#406"
                                                                                                                               (ty.bool)
                                                                                                                               (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 9) ([bv 37])))))
                                                                                                                               (stm_let "ж4069"
                                                                                                                                        (ty.bool)
                                                                                                                                        (stm_exp (exp_var "ga#406"))
                                                                                                                                        (stm_if ((stm_exp (exp_var "ж4069")))
                                                                                                                                                (stm_exp (exp_true))
                                                                                                                                                (stm_let "ga#407"
                                                                                                                                                         (ty.bool)
                                                                                                                                                         (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 9) ([bv 38])))))
                                                                                                                                                         (stm_let "ж4068"
                                                                                                                                                                  (ty.bool)
                                                                                                                                                                  (stm_exp (exp_var "ga#407"))
                                                                                                                                                                  (stm_if ((stm_exp (exp_var "ж4068")))
                                                                                                                                                                          (stm_exp (exp_true))
                                                                                                                                                                          (stm_let "ga#408"
                                                                                                                                                                                   (ty.bool)
                                                                                                                                                                                   (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 9) ([bv 35])))))
                                                                                                                                                                                   (stm_let "ж4067"
                                                                                                                                                                                            (ty.bool)
                                                                                                                                                                                            (stm_exp (exp_var "ga#408"))
                                                                                                                                                                                            (stm_if ((stm_exp (exp_var "ж4067")))
                                                                                                                                                                                                    (stm_exp (exp_true))
                                                                                                                                                                                                    (stm_exp (exp_false))))))))))))))))))))))).
    
    (*
      Extended type
        parameter offset
          ?[55:10]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_jeq_inst : Stm [
                                    "offset"  ∷  ty.bvec (10)
                                  ]
                                  (ty.unit) :=
      stm_let "ga#409"
              (ty.bool)
              (stm_call zerobitSet (env.snoc (env.nil)
                                             (_::_)
                                             ((exp_val (ty.unit) (tt)))%exp))
              (stm_let "ж4076"
                       (ty.bool)
                       (stm_exp (exp_var "ga#409"))
                       (stm_if ((stm_exp (exp_var "ж4076")))
                               (stm_seq (stm_let "ж4074"
                                                 (ty.wordBits)
                                                 (stm_let "ga#411"
                                                          (ty.bvec (16))
                                                          (stm_let "ga#410"
                                                                   (ty.bvec (10))
                                                                   (stm_call shiftl (env.snoc (env.snoc (env.nil)
                                                                                                        (_::_)
                                                                                                        ((exp_var "offset"))%exp)
                                                                                              (_::_)
                                                                                              ((exp_int 1%Z))%exp))
                                                                   (stm_exp (exp_unop (uop.sext (n := 16)) (exp_var "ga#410"))))
                                                          (stm_let "жreg_PC_reg_4075"
                                                                   (ty.wordBits)
                                                                   (stm_read_register PC_reg)
                                                                   (stm_exp (exp_binop bop.bvadd (exp_var "жreg_PC_reg_4075") (exp_var "ga#411")))))
                                                 (stm_write_register PC_reg (exp_var "ж4074")))
                                        (stm_exp (exp_val (ty.unit) (tt))))
                               (stm_exp (exp_val (ty.unit) (tt))))).
    
    (*
      Extended type
        parameter offset
          ?[56:10]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_jne_inst : Stm [
                                    "offset"  ∷  ty.bvec (10)
                                  ]
                                  (ty.unit) :=
      stm_let "ga#413"
              (ty.bool)
              (stm_let "ga#412"
                       (ty.bool)
                       (stm_call zerobitSet (env.snoc (env.nil)
                                                      (_::_)
                                                      ((exp_val (ty.unit) (tt)))%exp))
                       (stm_exp (exp_unop uop.not (exp_var "ga#412"))))
              (stm_let "ж4079"
                       (ty.bool)
                       (stm_exp (exp_var "ga#413"))
                       (stm_if ((stm_exp (exp_var "ж4079")))
                               (stm_seq (stm_let "ж4077"
                                                 (ty.wordBits)
                                                 (stm_let "ga#415"
                                                          (ty.bvec (16))
                                                          (stm_let "ga#414"
                                                                   (ty.bvec (10))
                                                                   (stm_call shiftl (env.snoc (env.snoc (env.nil)
                                                                                                        (_::_)
                                                                                                        ((exp_var "offset"))%exp)
                                                                                              (_::_)
                                                                                              ((exp_int 1%Z))%exp))
                                                                   (stm_exp (exp_unop (uop.sext (n := 16)) (exp_var "ga#414"))))
                                                          (stm_let "жreg_PC_reg_4078"
                                                                   (ty.wordBits)
                                                                   (stm_read_register PC_reg)
                                                                   (stm_exp (exp_binop bop.bvadd (exp_var "жreg_PC_reg_4078") (exp_var "ga#415")))))
                                                 (stm_write_register PC_reg (exp_var "ж4077")))
                                        (stm_exp (exp_val (ty.unit) (tt))))
                               (stm_exp (exp_val (ty.unit) (tt))))).
    
    (*
      Extended type
        parameter offset
          ?[57:10]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_jc_inst : Stm [
                                   "offset"  ∷  ty.bvec (10)
                                 ]
                                 (ty.unit) :=
      stm_let "ga#416"
              (ty.bool)
              (stm_call carrybitSet (env.snoc (env.nil)
                                              (_::_)
                                              ((exp_val (ty.unit) (tt)))%exp))
              (stm_let "ж4082"
                       (ty.bool)
                       (stm_exp (exp_var "ga#416"))
                       (stm_if ((stm_exp (exp_var "ж4082")))
                               (stm_seq (stm_let "ж4080"
                                                 (ty.wordBits)
                                                 (stm_let "ga#418"
                                                          (ty.bvec (16))
                                                          (stm_let "ga#417"
                                                                   (ty.bvec (10))
                                                                   (stm_call shiftl (env.snoc (env.snoc (env.nil)
                                                                                                        (_::_)
                                                                                                        ((exp_var "offset"))%exp)
                                                                                              (_::_)
                                                                                              ((exp_int 1%Z))%exp))
                                                                   (stm_exp (exp_unop (uop.sext (n := 16)) (exp_var "ga#417"))))
                                                          (stm_let "жreg_PC_reg_4081"
                                                                   (ty.wordBits)
                                                                   (stm_read_register PC_reg)
                                                                   (stm_exp (exp_binop bop.bvadd (exp_var "жreg_PC_reg_4081") (exp_var "ga#418")))))
                                                 (stm_write_register PC_reg (exp_var "ж4080")))
                                        (stm_exp (exp_val (ty.unit) (tt))))
                               (stm_exp (exp_val (ty.unit) (tt))))).
    
    (*
      Extended type
        parameter offset
          ?[58:10]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_jnc_inst : Stm [
                                    "offset"  ∷  ty.bvec (10)
                                  ]
                                  (ty.unit) :=
      stm_let "ga#420"
              (ty.bool)
              (stm_let "ga#419"
                       (ty.bool)
                       (stm_call carrybitSet (env.snoc (env.nil)
                                                       (_::_)
                                                       ((exp_val (ty.unit) (tt)))%exp))
                       (stm_exp (exp_unop uop.not (exp_var "ga#419"))))
              (stm_let "ж4085"
                       (ty.bool)
                       (stm_exp (exp_var "ga#420"))
                       (stm_if ((stm_exp (exp_var "ж4085")))
                               (stm_seq (stm_let "ж4083"
                                                 (ty.wordBits)
                                                 (stm_let "ga#422"
                                                          (ty.bvec (16))
                                                          (stm_let "ga#421"
                                                                   (ty.bvec (10))
                                                                   (stm_call shiftl (env.snoc (env.snoc (env.nil)
                                                                                                        (_::_)
                                                                                                        ((exp_var "offset"))%exp)
                                                                                              (_::_)
                                                                                              ((exp_int 1%Z))%exp))
                                                                   (stm_exp (exp_unop (uop.sext (n := 16)) (exp_var "ga#421"))))
                                                          (stm_let "жreg_PC_reg_4084"
                                                                   (ty.wordBits)
                                                                   (stm_read_register PC_reg)
                                                                   (stm_exp (exp_binop bop.bvadd (exp_var "жreg_PC_reg_4084") (exp_var "ga#422")))))
                                                 (stm_write_register PC_reg (exp_var "ж4083")))
                                        (stm_exp (exp_val (ty.unit) (tt))))
                               (stm_exp (exp_val (ty.unit) (tt))))).
    
    (*
      Extended type
        parameter offset
          ?[59:10]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_jn_inst : Stm [
                                   "offset"  ∷  ty.bvec (10)
                                 ]
                                 (ty.unit) :=
      stm_let "ga#423"
              (ty.bool)
              (stm_call negativebitSet (env.snoc (env.nil)
                                                 (_::_)
                                                 ((exp_val (ty.unit) (tt)))%exp))
              (stm_let "ж4088"
                       (ty.bool)
                       (stm_exp (exp_var "ga#423"))
                       (stm_if ((stm_exp (exp_var "ж4088")))
                               (stm_seq (stm_let "ж4086"
                                                 (ty.wordBits)
                                                 (stm_let "ga#425"
                                                          (ty.bvec (16))
                                                          (stm_let "ga#424"
                                                                   (ty.bvec (10))
                                                                   (stm_call shiftl (env.snoc (env.snoc (env.nil)
                                                                                                        (_::_)
                                                                                                        ((exp_var "offset"))%exp)
                                                                                              (_::_)
                                                                                              ((exp_int 1%Z))%exp))
                                                                   (stm_exp (exp_unop (uop.sext (n := 16)) (exp_var "ga#424"))))
                                                          (stm_let "жreg_PC_reg_4087"
                                                                   (ty.wordBits)
                                                                   (stm_read_register PC_reg)
                                                                   (stm_exp (exp_binop bop.bvadd (exp_var "жreg_PC_reg_4087") (exp_var "ga#425")))))
                                                 (stm_write_register PC_reg (exp_var "ж4086")))
                                        (stm_exp (exp_val (ty.unit) (tt))))
                               (stm_exp (exp_val (ty.unit) (tt))))).
    
    (*
      Extended type
        parameter offset
          ?[60:10]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_jge_inst : Stm [
                                    "offset"  ∷  ty.bvec (10)
                                  ]
                                  (ty.unit) :=
      stm_let "ga#429"
              (ty.bool)
              (stm_let "ga#428"
                       (ty.bool)
                       (stm_let "ga#426"
                                (ty.bool)
                                (stm_call overflowbitSet (env.snoc (env.nil)
                                                                   (_::_)
                                                                   ((exp_val (ty.unit) (tt)))%exp))
                                (stm_let "ga#427"
                                         (ty.bool)
                                         (stm_call negativebitSet (env.snoc (env.nil)
                                                                            (_::_)
                                                                            ((exp_val (ty.unit) (tt)))%exp))
                                         (stm_call xor_bool (env.snoc (env.snoc (env.nil)
                                                                                (_::_)
                                                                                ((exp_var "ga#426"))%exp)
                                                                      (_::_)
                                                                      ((exp_var "ga#427"))%exp))))
                       (stm_exp (exp_unop uop.not (exp_var "ga#428"))))
              (stm_let "ж4091"
                       (ty.bool)
                       (stm_exp (exp_var "ga#429"))
                       (stm_if ((stm_exp (exp_var "ж4091")))
                               (stm_seq (stm_let "ж4089"
                                                 (ty.wordBits)
                                                 (stm_let "ga#431"
                                                          (ty.bvec (16))
                                                          (stm_let "ga#430"
                                                                   (ty.bvec (10))
                                                                   (stm_call shiftl (env.snoc (env.snoc (env.nil)
                                                                                                        (_::_)
                                                                                                        ((exp_var "offset"))%exp)
                                                                                              (_::_)
                                                                                              ((exp_int 1%Z))%exp))
                                                                   (stm_exp (exp_unop (uop.sext (n := 16)) (exp_var "ga#430"))))
                                                          (stm_let "жreg_PC_reg_4090"
                                                                   (ty.wordBits)
                                                                   (stm_read_register PC_reg)
                                                                   (stm_exp (exp_binop bop.bvadd (exp_var "жreg_PC_reg_4090") (exp_var "ga#431")))))
                                                 (stm_write_register PC_reg (exp_var "ж4089")))
                                        (stm_exp (exp_val (ty.unit) (tt))))
                               (stm_exp (exp_val (ty.unit) (tt))))).
    
    (*
      Extended type
        parameter offset
          ?[61:10]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_jl_inst : Stm [
                                   "offset"  ∷  ty.bvec (10)
                                 ]
                                 (ty.unit) :=
      stm_let "ga#434"
              (ty.bool)
              (stm_let "ga#432"
                       (ty.bool)
                       (stm_call overflowbitSet (env.snoc (env.nil)
                                                          (_::_)
                                                          ((exp_val (ty.unit) (tt)))%exp))
                       (stm_let "ga#433"
                                (ty.bool)
                                (stm_call negativebitSet (env.snoc (env.nil)
                                                                   (_::_)
                                                                   ((exp_val (ty.unit) (tt)))%exp))
                                (stm_call xor_bool (env.snoc (env.snoc (env.nil)
                                                                       (_::_)
                                                                       ((exp_var "ga#432"))%exp)
                                                             (_::_)
                                                             ((exp_var "ga#433"))%exp))))
              (stm_let "ж4094"
                       (ty.bool)
                       (stm_exp (exp_var "ga#434"))
                       (stm_if ((stm_exp (exp_var "ж4094")))
                               (stm_seq (stm_let "ж4092"
                                                 (ty.wordBits)
                                                 (stm_let "ga#436"
                                                          (ty.bvec (16))
                                                          (stm_let "ga#435"
                                                                   (ty.bvec (10))
                                                                   (stm_call shiftl (env.snoc (env.snoc (env.nil)
                                                                                                        (_::_)
                                                                                                        ((exp_var "offset"))%exp)
                                                                                              (_::_)
                                                                                              ((exp_int 1%Z))%exp))
                                                                   (stm_exp (exp_unop (uop.sext (n := 16)) (exp_var "ga#435"))))
                                                          (stm_let "жreg_PC_reg_4093"
                                                                   (ty.wordBits)
                                                                   (stm_read_register PC_reg)
                                                                   (stm_exp (exp_binop bop.bvadd (exp_var "жreg_PC_reg_4093") (exp_var "ga#436")))))
                                                 (stm_write_register PC_reg (exp_var "ж4092")))
                                        (stm_exp (exp_val (ty.unit) (tt))))
                               (stm_exp (exp_val (ty.unit) (tt))))).
    
    (*
      Extended type
        parameter offset
          ?[62:10]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_jmp_inst : Stm [
                                    "offset"  ∷  ty.bvec (10)
                                  ]
                                  (ty.unit) :=
      stm_seq (stm_let "ж4095"
                       (ty.wordBits)
                       (stm_let "ga#438"
                                (ty.bvec (16))
                                (stm_let "ga#437"
                                         (ty.bvec (10))
                                         (stm_call shiftl (env.snoc (env.snoc (env.nil)
                                                                              (_::_)
                                                                              ((exp_var "offset"))%exp)
                                                                    (_::_)
                                                                    ((exp_int 1%Z))%exp))
                                         (stm_exp (exp_unop (uop.sext (n := 16)) (exp_var "ga#437"))))
                                (stm_let "жreg_PC_reg_4096"
                                         (ty.wordBits)
                                         (stm_read_register PC_reg)
                                         (stm_exp (exp_binop bop.bvadd (exp_var "жreg_PC_reg_4096") (exp_var "ga#438")))))
                       (stm_write_register PC_reg (exp_var "ж4095")))
              (stm_exp (exp_val (ty.unit) (tt))).
    
    (*
      Extended type
        parameter arg#
          jump
        return value
          ?[63]
      
      [0] : Sail type: bitvector(3)
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_encdec_jump_forwards : Stm [
                                                "arg#"  ∷  ty.enum Ejump
                                              ]
                                              (ty.bvec (3)) :=
      stm_let "ж4097"
              (ty.enum Ejump)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Ejump
                              (stm_exp (exp_var "ж4097"))
                              (fun K => match K with
                                        | JC  => stm_exp (exp_val (ty.bvec 3) ([bv 3]))
                                        | JEQ => stm_exp (exp_val (ty.bvec 3) ([bv 1]))
                                        | JGE => stm_exp (exp_val (ty.bvec 3) ([bv 5]))
                                        | JL  => stm_exp (exp_val (ty.bvec 3) ([bv 6]))
                                        | JMP => stm_exp (exp_val (ty.bvec 3) ([bv 7]))
                                        | JN  => stm_exp (exp_val (ty.bvec 3) ([bv 4]))
                                        | JNC => stm_exp (exp_val (ty.bvec 3) ([bv 2]))
                                        | JNE => stm_exp (exp_val (ty.bvec 3) ([bv 0]))
                                        end)).
    
    (*
      Extended type
        parameter arg#
          ?[64:3]
        return value
          jump
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_encdec_jump_backwards : Stm [
                                                 "arg#"  ∷  ty.bvec (3)
                                               ]
                                               (ty.enum Ejump) :=
      stm_let "b__0"
              (ty.bvec (3))
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#439"
                       (ty.bool)
                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 1])))))
                       (stm_let "ж4113"
                                (ty.bool)
                                (stm_exp (exp_var "ga#439"))
                                (stm_if ((stm_exp (exp_var "ж4113")))
                                        (stm_exp (exp_val (ty.enum Ejump) (JEQ)))
                                        (stm_let "ga#440"
                                                 (ty.bool)
                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 0])))))
                                                 (stm_let "ж4112"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#440"))
                                                          (stm_if ((stm_exp (exp_var "ж4112")))
                                                                  (stm_exp (exp_val (ty.enum Ejump) (JNE)))
                                                                  (stm_let "ga#441"
                                                                           (ty.bool)
                                                                           (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 3])))))
                                                                           (stm_let "ж4111"
                                                                                    (ty.bool)
                                                                                    (stm_exp (exp_var "ga#441"))
                                                                                    (stm_if ((stm_exp (exp_var "ж4111")))
                                                                                            (stm_exp (exp_val (ty.enum Ejump) (JC)))
                                                                                            (stm_let "ga#442"
                                                                                                     (ty.bool)
                                                                                                     (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 2])))))
                                                                                                     (stm_let "ж4110"
                                                                                                              (ty.bool)
                                                                                                              (stm_exp (exp_var "ga#442"))
                                                                                                              (stm_if ((stm_exp (exp_var "ж4110")))
                                                                                                                      (stm_exp (exp_val (ty.enum Ejump) (JNC)))
                                                                                                                      (stm_let "ga#443"
                                                                                                                               (ty.bool)
                                                                                                                               (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 4])))))
                                                                                                                               (stm_let "ж4109"
                                                                                                                                        (ty.bool)
                                                                                                                                        (stm_exp (exp_var "ga#443"))
                                                                                                                                        (stm_if ((stm_exp (exp_var "ж4109")))
                                                                                                                                                (stm_exp (exp_val (ty.enum Ejump) (JN)))
                                                                                                                                                (stm_let "ga#444"
                                                                                                                                                         (ty.bool)
                                                                                                                                                         (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 5])))))
                                                                                                                                                         (stm_let "ж4108"
                                                                                                                                                                  (ty.bool)
                                                                                                                                                                  (stm_exp (exp_var "ga#444"))
                                                                                                                                                                  (stm_if ((stm_exp (exp_var "ж4108")))
                                                                                                                                                                          (stm_exp (exp_val (ty.enum Ejump) (JGE)))
                                                                                                                                                                          (stm_let "ga#445"
                                                                                                                                                                                   (ty.bool)
                                                                                                                                                                                   (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 6])))))
                                                                                                                                                                                   (stm_let "ж4107"
                                                                                                                                                                                            (ty.bool)
                                                                                                                                                                                            (stm_exp (exp_var "ga#445"))
                                                                                                                                                                                            (stm_if ((stm_exp (exp_var "ж4107")))
                                                                                                                                                                                                    (stm_exp (exp_val (ty.enum Ejump) (JL)))
                                                                                                                                                                                                    (stm_exp (exp_val (ty.enum Ejump) (JMP)))))))))))))))))))))))).
    
    (*
      Extended type
        parameter arg#
          jump
        return value
          $0
    *)
    Definition fun_encdec_jump_forwards_matches : Stm [
                                                        "arg#"  ∷  ty.enum Ejump
                                                      ]
                                                      (ty.bool) :=
      stm_let "ж4114"
              (ty.enum Ejump)
              (stm_exp (exp_var "arg#"))
              (stm_match_enum Ejump
                              (stm_exp (exp_var "ж4114"))
                              (fun K => match K with
                                        | JC  => stm_exp (exp_true)
                                        | JEQ => stm_exp (exp_true)
                                        | JGE => stm_exp (exp_true)
                                        | JL  => stm_exp (exp_true)
                                        | JMP => stm_exp (exp_true)
                                        | JN  => stm_exp (exp_true)
                                        | JNC => stm_exp (exp_true)
                                        | JNE => stm_exp (exp_true)
                                        end)).
    
    (*
      Extended type
        parameter arg#
          ?[65:3]
        return value
          $0
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_encdec_jump_backwards_matches : Stm [
                                                         "arg#"  ∷  ty.bvec (3)
                                                       ]
                                                       (ty.bool) :=
      stm_let "b__0"
              (ty.bvec (3))
              (stm_exp (exp_var "arg#"))
              (stm_let "ga#446"
                       (ty.bool)
                       (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 1])))))
                       (stm_let "ж4131"
                                (ty.bool)
                                (stm_exp (exp_var "ga#446"))
                                (stm_if ((stm_exp (exp_var "ж4131")))
                                        (stm_exp (exp_true))
                                        (stm_let "ga#447"
                                                 (ty.bool)
                                                 (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 0])))))
                                                 (stm_let "ж4130"
                                                          (ty.bool)
                                                          (stm_exp (exp_var "ga#447"))
                                                          (stm_if ((stm_exp (exp_var "ж4130")))
                                                                  (stm_exp (exp_true))
                                                                  (stm_let "ga#448"
                                                                           (ty.bool)
                                                                           (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 3])))))
                                                                           (stm_let "ж4129"
                                                                                    (ty.bool)
                                                                                    (stm_exp (exp_var "ga#448"))
                                                                                    (stm_if ((stm_exp (exp_var "ж4129")))
                                                                                            (stm_exp (exp_true))
                                                                                            (stm_let "ga#449"
                                                                                                     (ty.bool)
                                                                                                     (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 2])))))
                                                                                                     (stm_let "ж4128"
                                                                                                              (ty.bool)
                                                                                                              (stm_exp (exp_var "ga#449"))
                                                                                                              (stm_if ((stm_exp (exp_var "ж4128")))
                                                                                                                      (stm_exp (exp_true))
                                                                                                                      (stm_let "ga#450"
                                                                                                                               (ty.bool)
                                                                                                                               (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 4])))))
                                                                                                                               (stm_let "ж4127"
                                                                                                                                        (ty.bool)
                                                                                                                                        (stm_exp (exp_var "ga#450"))
                                                                                                                                        (stm_if ((stm_exp (exp_var "ж4127")))
                                                                                                                                                (stm_exp (exp_true))
                                                                                                                                                (stm_let "ga#451"
                                                                                                                                                         (ty.bool)
                                                                                                                                                         (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 5])))))
                                                                                                                                                         (stm_let "ж4126"
                                                                                                                                                                  (ty.bool)
                                                                                                                                                                  (stm_exp (exp_var "ga#451"))
                                                                                                                                                                  (stm_if ((stm_exp (exp_var "ж4126")))
                                                                                                                                                                          (stm_exp (exp_true))
                                                                                                                                                                          (stm_let "ga#452"
                                                                                                                                                                                   (ty.bool)
                                                                                                                                                                                   (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 6])))))
                                                                                                                                                                                   (stm_let "ж4125"
                                                                                                                                                                                            (ty.bool)
                                                                                                                                                                                            (stm_exp (exp_var "ga#452"))
                                                                                                                                                                                            (stm_if ((stm_exp (exp_var "ж4125")))
                                                                                                                                                                                                    (stm_exp (exp_true))
                                                                                                                                                                                                    (stm_let "ga#453"
                                                                                                                                                                                                             (ty.bool)
                                                                                                                                                                                                             (stm_exp (((exp_var "b__0") = (exp_val (ty.bvec 3) ([bv 7])))))
                                                                                                                                                                                                             (stm_let "ж4124"
                                                                                                                                                                                                                      (ty.bool)
                                                                                                                                                                                                                      (stm_exp (exp_var "ga#453"))
                                                                                                                                                                                                                      (stm_if ((stm_exp (exp_var "ж4124")))
                                                                                                                                                                                                                              (stm_exp (exp_true))
                                                                                                                                                                                                                              (stm_exp (exp_false)))))))))))))))))))))))))).
    
    (*
      Extended type
        parameter merge#var
          ast
        return value
          string
    *)
    Definition fun_formatAst : Stm [
                                     "merge#var"  ∷  ty.union Uast
                                   ]
                                   (ty.string).
      refine (
      stm_let "ж4132"
              (ty.union Uast)
              (stm_exp (exp_var "merge#var"))
              (stm_match_union_alt_list Uast
                                        (stm_exp (exp_var "ж4132"))
                                        [
                                          existT Kdoesnotunderstand (MkAlt (pat_var "ж4154") (stm_seq (stm_assert (exp_false) (exp_string "Pattern match failure at ../msp430-ipe-sail/instructions/jumps.sail:69.0-71.1"))
                                                                                                       (stm_fail _ "failure")));
                                          existT Kdoubleop (MkAlt (pat_tuple ("op", "bw", "sourceReg", "As", "destinationReg", "Ad")) (stm_let "ga#463"
                                                                                                                                               (ty.string)
                                                                                                                                               (stm_let "ga#462"
                                                                                                                                                        (ty.string)
                                                                                                                                                        (stm_let "ga#460"
                                                                                                                                                                 (ty.string)
                                                                                                                                                                 (stm_let "ga#459"
                                                                                                                                                                          (ty.string)
                                                                                                                                                                          (stm_let "ga#457"
                                                                                                                                                                                   (ty.string)
                                                                                                                                                                                   (stm_let "ga#456"
                                                                                                                                                                                            (ty.string)
                                                                                                                                                                                            (stm_let "ga#454"
                                                                                                                                                                                                     (ty.string)
                                                                                                                                                                                                     (stm_call duopName (env.snoc (env.nil)
                                                                                                                                                                                                                                  (_::_)
                                                                                                                                                                                                                                  ((exp_var "op"))%exp))
                                                                                                                                                                                                     (stm_let "ga#455"
                                                                                                                                                                                                              (ty.string)
                                                                                                                                                                                                              (stm_call BWstring (env.snoc (env.nil)
                                                                                                                                                                                                                                           (_::_)
                                                                                                                                                                                                                                           ((exp_var "bw"))%exp))
                                                                                                                                                                                                              (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                                                                       (_::_)
                                                                                                                                                                                                                                                       ((exp_var "ga#454"))%exp)
                                                                                                                                                                                                                                             (_::_)
                                                                                                                                                                                                                                             ((exp_var "ga#455"))%exp))))
                                                                                                                                                                                            (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                                                     (_::_)
                                                                                                                                                                                                                                     ((exp_var "ga#456"))%exp)
                                                                                                                                                                                                                           (_::_)
                                                                                                                                                                                                                           ((exp_string " "))%exp)))
                                                                                                                                                                                   (stm_let "ga#458"
                                                                                                                                                                                            (ty.string)
                                                                                                                                                                                            (stm_call regName (env.snoc (env.nil)
                                                                                                                                                                                                                        (_::_)
                                                                                                                                                                                                                        ((exp_var "sourceReg"))%exp))
                                                                                                                                                                                            (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                                                     (_::_)
                                                                                                                                                                                                                                     ((exp_var "ga#457"))%exp)
                                                                                                                                                                                                                           (_::_)
                                                                                                                                                                                                                           ((exp_var "ga#458"))%exp))))
                                                                                                                                                                          (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                                   (_::_)
                                                                                                                                                                                                                   ((exp_var "ga#459"))%exp)
                                                                                                                                                                                                         (_::_)
                                                                                                                                                                                                         ((exp_string "("))%exp)))
                                                                                                                                                                 (stm_let "ga#461"
                                                                                                                                                                          (ty.string)
                                                                                                                                                                          (stm_call AMstring (env.snoc (env.nil)
                                                                                                                                                                                                       (_::_)
                                                                                                                                                                                                       ((exp_var "As"))%exp))
                                                                                                                                                                          (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                                   (_::_)
                                                                                                                                                                                                                   ((exp_var "ga#460"))%exp)
                                                                                                                                                                                                         (_::_)
                                                                                                                                                                                                         ((exp_var "ga#461"))%exp))))
                                                                                                                                                        (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                 (_::_)
                                                                                                                                                                                                 ((exp_var "ga#462"))%exp)
                                                                                                                                                                                       (_::_)
                                                                                                                                                                                       ((exp_string ")"))%exp)))
                                                                                                                                               (stm_let "ga#464"
                                                                                                                                                        (ty.string)
                                                                                                                                                        (stm_call regName (env.snoc (env.nil)
                                                                                                                                                                                    (_::_)
                                                                                                                                                                                    ((exp_var "destinationReg"))%exp))
                                                                                                                                                        (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                 (_::_)
                                                                                                                                                                                                 ((exp_var "ga#463"))%exp)
                                                                                                                                                                                       (_::_)
                                                                                                                                                                                       ((exp_var "ga#464"))%exp)))));
                                          existT Kjump (MkAlt (pat_pair "op" "offset") (stm_let "ga#475"
                                                                                                (ty.string)
                                                                                                (stm_let "ga#474"
                                                                                                         (ty.string)
                                                                                                         (stm_call jumpName (env.snoc (env.nil)
                                                                                                                                      (_::_)
                                                                                                                                      ((exp_var "op"))%exp))
                                                                                                         (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                  (_::_)
                                                                                                                                                  ((exp_var "ga#474"))%exp)
                                                                                                                                        (_::_)
                                                                                                                                        ((exp_string " "))%exp)))
                                                                                                (stm_let "ga#476"
                                                                                                         (ty.string)
                                                                                                         (stm_call bits_str (env.snoc (env.nil)
                                                                                                                                      (_::_)
                                                                                                                                      ((exp_var "offset"))%exp))
                                                                                                         (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                  (_::_)
                                                                                                                                                  ((exp_var "ga#475"))%exp)
                                                                                                                                        (_::_)
                                                                                                                                        ((exp_var "ga#476"))%exp)))));
                                          existT Ksingleop (MkAlt (pat_tuple ("op", "bw", "As", "reg")) (stm_let "ga#473"
                                                                                                                 (ty.string)
                                                                                                                 (stm_let "ga#471"
                                                                                                                          (ty.string)
                                                                                                                          (stm_let "ga#470"
                                                                                                                                   (ty.string)
                                                                                                                                   (stm_let "ga#468"
                                                                                                                                            (ty.string)
                                                                                                                                            (stm_let "ga#467"
                                                                                                                                                     (ty.string)
                                                                                                                                                     (stm_let "ga#465"
                                                                                                                                                              (ty.string)
                                                                                                                                                              (stm_call singleopName (env.snoc (env.nil)
                                                                                                                                                                                               (_::_)
                                                                                                                                                                                               ((exp_var "op"))%exp))
                                                                                                                                                              (stm_let "ga#466"
                                                                                                                                                                       (ty.string)
                                                                                                                                                                       (stm_call BWstring (env.snoc (env.nil)
                                                                                                                                                                                                    (_::_)
                                                                                                                                                                                                    ((exp_var "bw"))%exp))
                                                                                                                                                                       (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                                (_::_)
                                                                                                                                                                                                                ((exp_var "ga#465"))%exp)
                                                                                                                                                                                                      (_::_)
                                                                                                                                                                                                      ((exp_var "ga#466"))%exp))))
                                                                                                                                                     (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                              (_::_)
                                                                                                                                                                                              ((exp_var "ga#467"))%exp)
                                                                                                                                                                                    (_::_)
                                                                                                                                                                                    ((exp_string " "))%exp)))
                                                                                                                                            (stm_let "ga#469"
                                                                                                                                                     (ty.string)
                                                                                                                                                     (stm_call regName (env.snoc (env.nil)
                                                                                                                                                                                 (_::_)
                                                                                                                                                                                 ((exp_var "reg"))%exp))
                                                                                                                                                     (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                              (_::_)
                                                                                                                                                                                              ((exp_var "ga#468"))%exp)
                                                                                                                                                                                    (_::_)
                                                                                                                                                                                    ((exp_var "ga#469"))%exp))))
                                                                                                                                   (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                                            (_::_)
                                                                                                                                                                            ((exp_var "ga#470"))%exp)
                                                                                                                                                                  (_::_)
                                                                                                                                                                  ((exp_string "("))%exp)))
                                                                                                                          (stm_let "ga#472"
                                                                                                                                   (ty.string)
                                                                                                                                   (stm_call AMstring (env.snoc (env.nil)
                                                                                                                                                                (_::_)
                                                                                                                                                                ((exp_var "As"))%exp))
                                                                                                                                   (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                                            (_::_)
                                                                                                                                                                            ((exp_var "ga#471"))%exp)
                                                                                                                                                                  (_::_)
                                                                                                                                                                  ((exp_var "ga#472"))%exp))))
                                                                                                                 (stm_call concat_str (env.snoc (env.snoc (env.nil)
                                                                                                                                                          (_::_)
                                                                                                                                                          ((exp_var "ga#473"))%exp)
                                                                                                                                                (_::_)
                                                                                                                                                ((exp_string ")"))%exp))))
                                        ]
                                        Logic.I)).
      cbn.
      (* ty.Address is bvec 16 *)
      (* ty.Offset is bvec 10 *)
    Restart.
      refine (stm_fail _ "").
    Defined.

    (*
      Extended type
        parameter arg#
          ast
        return value
          ?[67]
      
      [0] : Not yet implemented; see nanosail/NanosailToMicrosail/FunctionCalls.ml line 498 (expected constant in bitvector type)
      
      [1] : Sail type: bitvector(16)
            OCaml position: nanosail/SailToNanosail/Translate/ExtendedType.ml line 483
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_encdec_forwards : Stm [
                                           "arg#"  ∷  ty.union Uast
                                         ]
                                         (ty.bvec (16)) :=
      stm_fail _ "".
    
    (*
      Extended type
        parameter arg#
          ast
        return value
          $0
    *)
    Definition fun_encdec_forwards_matches : Stm [
                                                   "arg#"  ∷  ty.union Uast
                                                 ]
                                                 (ty.bool) :=
      stm_let "ж4174"
              (ty.union Uast)
              (stm_exp (exp_var "arg#"))
              (stm_match_union_alt_list Uast
                                        (stm_exp (exp_var "ж4174"))
                                        [
                                          existT Kdoesnotunderstand (MkAlt (pat_var "a") (stm_exp (exp_true)));
                                          existT Kdoubleop (MkAlt (pat_tuple ("op", "bw", "sourceReg", "As", "destinationReg", "Ad")) (stm_exp (exp_true)));
                                          existT Kjump (MkAlt (pat_pair "op" "offset") (stm_exp (exp_true)));
                                          existT Ksingleop (MkAlt (pat_tuple ("op", "bw", "As", "reg")) (stm_exp (exp_true)))
                                        ]
                                        Logic.I).
    
    (*
      Extended type
        parameter op
          singleop
        parameter BW
          BW
        parameter addressingMode
          AM
        parameter reg
          Register
        return value
          unit
    *)
    Definition fun_execute_SINGLEOP : Stm [
                                            "op"  ∷  ty.enum Esingleop;
                                            "BW"  ∷  ty.enum Ebw;
                                            "addressingMode"  ∷  ty.enum Eam;
                                            "reg"  ∷  ty.enum Eregister
                                          ]
                                          (ty.unit) :=
      stm_seq (stm_let "ga#559"
                       (ty.string)
                       (stm_let "ga#558"
                                ((ty.union Uast))
                                (stm_exp (exp_union Uast Ksingleop (exp_tuple [
                                                                                exp_var "op";
                                                                                exp_var "BW";
                                                                                exp_var "addressingMode";
                                                                                exp_var "reg"
                                                                              ])))
                                (stm_call formatAst (env.snoc (env.nil)
                                                              (_::_)
                                                              ((exp_var "ga#558"))%exp)))
                       (stm_call logWithVerbosity (env.snoc (env.snoc (env.nil)
                                                                      (_::_)
                                                                      ((exp_int 2%Z))%exp)
                                                            (_::_)
                                                            ((exp_var "ga#559"))%exp)))
              (stm_let "ж4194"
                       (ty.enum Esingleop)
                       (stm_exp (exp_var "op"))
                       (stm_match_enum Esingleop
                                       (stm_exp (exp_var "ж4194"))
                                       (fun K => match K with
                                                 | CALL => stm_call call_inst (env.snoc (env.nil)
                                                                                        (_::ty.tuple _)
                                                                                        (exp_tuple [ exp_var "BW"; exp_var "addressingMode"; exp_var "reg" ]))
                                                 | PUSH => stm_call push_inst (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                            (_::_)
                                                                                                            ((exp_var "BW"))%exp)
                                                                                                  (_::_)
                                                                                                  ((exp_var "addressingMode"))%exp)
                                                                                        (_::_)
                                                                                        ((exp_var "reg"))%exp)
                                                 | RETI => stm_call reti_inst (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                            (_::_)
                                                                                                            ((exp_var "BW"))%exp)
                                                                                                  (_::_)
                                                                                                  ((exp_var "addressingMode"))%exp)
                                                                                        (_::_)
                                                                                        ((exp_var "reg"))%exp)
                                                 | RRA  => stm_call rra_inst (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                           (_::_)
                                                                                                           ((exp_var "BW"))%exp)
                                                                                                 (_::_)
                                                                                                 ((exp_var "addressingMode"))%exp)
                                                                                       (_::_)
                                                                                       ((exp_var "reg"))%exp)
                                                 | RRC  => stm_call rrc_inst (env.snoc (env.nil)
                                                                                       (_:: ty.tuple _)
                                                                                       (exp_tuple [ exp_var "BW"; exp_var "addressingMode"; exp_var "reg" ]))
                                                 | SWPB => stm_call swpb_inst (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                            (_::_)
                                                                                                            ((exp_var "BW"))%exp)
                                                                                                  (_::_)
                                                                                                  ((exp_var "addressingMode"))%exp)
                                                                                        (_::_)
                                                                                        ((exp_var "reg"))%exp)
                                                 | SXT  => stm_call sxt_inst (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                           (_::_)
                                                                                                           ((exp_var "BW"))%exp)
                                                                                                 (_::_)
                                                                                                 ((exp_var "addressingMode"))%exp)
                                                                                       (_::_)
                                                                                       ((exp_var "reg"))%exp)
                                                 end))).
    
    (*
      Extended type
        parameter op
          jump
        parameter offset
          ?[68:10]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_execute_JUMP : Stm [
                                        "op"  ∷  ty.enum Ejump;
                                        "offset"  ∷  ty.bvec (10)
                                      ]
                                      (ty.unit) :=
      stm_seq (stm_let "ga#562"
                       (ty.string)
                       (stm_let "ga#561"
                                ((ty.union Uast))
                                (stm_exp (exp_union Uast Kjump (exp_binop bop.pair (exp_var "op") (exp_var "offset"))))
                                (stm_call formatAst (env.snoc (env.nil)
                                                              (_::_)
                                                              ((exp_var "ga#561"))%exp)))
                       (stm_call logWithVerbosity (env.snoc (env.snoc (env.nil)
                                                                      (_::_)
                                                                      ((exp_int 2%Z))%exp)
                                                            (_::_)
                                                            ((exp_var "ga#562"))%exp)))
              (stm_let "ж4206"
                       (ty.enum Ejump)
                       (stm_exp (exp_var "op"))
                       (stm_match_enum Ejump
                                       (stm_exp (exp_var "ж4206"))
                                       (fun K => match K with
                                                 | JC  => stm_call jc_inst (env.snoc (env.nil)
                                                                                     (_::_)
                                                                                     ((exp_var "offset"))%exp)
                                                 | JEQ => stm_call jeq_inst (env.snoc (env.nil)
                                                                                      (_::_)
                                                                                      ((exp_var "offset"))%exp)
                                                 | JGE => stm_call jge_inst (env.snoc (env.nil)
                                                                                      (_::_)
                                                                                      ((exp_var "offset"))%exp)
                                                 | JL  => stm_call jl_inst (env.snoc (env.nil)
                                                                                     (_::_)
                                                                                     ((exp_var "offset"))%exp)
                                                 | JMP => stm_call jmp_inst (env.snoc (env.nil)
                                                                                      (_::_)
                                                                                      ((exp_var "offset"))%exp)
                                                 | JN  => stm_call jn_inst (env.snoc (env.nil)
                                                                                     (_::_)
                                                                                     ((exp_var "offset"))%exp)
                                                 | JNC => stm_call jnc_inst (env.snoc (env.nil)
                                                                                      (_::_)
                                                                                      ((exp_var "offset"))%exp)
                                                 | JNE => stm_call jne_inst (env.snoc (env.nil)
                                                                                      (_::_)
                                                                                      ((exp_var "offset"))%exp)
                                                 end))).
    
    (*
      Extended type
        parameter op
          doubleop
        parameter BW
          BW
        parameter sourceRegister
          Register
        parameter addressingModeSource
          AM
        parameter destinationRegister
          Register
        parameter addressingModeDestination
          AM
        return value
          unit
    *)
    Definition fun_execute_DOUBLEOP : Stm [
                                            "op"  ∷  ty.enum Edoubleop;
                                            "BW"  ∷  ty.enum Ebw;
                                            "sourceRegister"  ∷  ty.enum Eregister;
                                            "addressingModeSource"  ∷  ty.enum Eam;
                                            "destinationRegister"  ∷  ty.enum Eregister;
                                            "addressingModeDestination"  ∷  ty.enum Eam
                                          ]
                                          (ty.unit) :=
      stm_seq (stm_let "ga#565"
                       (ty.string)
                       (stm_let "ga#564"
                                ((ty.union Uast))
                                (stm_exp (exp_union Uast Kdoubleop (exp_tuple [
                                                                                exp_var "op";
                                                                                exp_var "BW";
                                                                                exp_var "sourceRegister";
                                                                                exp_var "addressingModeSource";
                                                                                exp_var "destinationRegister";
                                                                                exp_var "addressingModeDestination"
                                                                              ])))
                                (stm_call formatAst (env.snoc (env.nil)
                                                              (_::_)
                                                              ((exp_var "ga#564"))%exp)))
                       (stm_call logWithVerbosity (env.snoc (env.snoc (env.nil)
                                                                      (_::_)
                                                                      ((exp_int 2%Z))%exp)
                                                            (_::_)
                                                            ((exp_var "ga#565"))%exp)))
              (stm_let "ж4219"
                       (ty.enum Edoubleop)
                       (stm_exp (exp_var "op"))
                       (stm_match_enum Edoubleop
                                       (stm_exp (exp_var "ж4219"))
                                       (fun K => match K with
                                                 | ADD  => stm_call add_inst (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                               (_::_)
                                                                                                                               ((exp_var "BW"))%exp)
                                                                                                                     (_::_)
                                                                                                                     ((exp_var "sourceRegister"))%exp)
                                                                                                           (_::_)
                                                                                                           ((exp_var "addressingModeSource"))%exp)
                                                                                                 (_::_)
                                                                                                 ((exp_var "destinationRegister"))%exp)
                                                                                       (_::_)
                                                                                       ((exp_var "addressingModeDestination"))%exp)
                                                 | ADDC => stm_call addc_inst (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                (_::_)
                                                                                                                                ((exp_var "BW"))%exp)
                                                                                                                      (_::_)
                                                                                                                      ((exp_var "sourceRegister"))%exp)
                                                                                                            (_::_)
                                                                                                            ((exp_var "addressingModeSource"))%exp)
                                                                                                  (_::_)
                                                                                                  ((exp_var "destinationRegister"))%exp)
                                                                                        (_::_)
                                                                                        ((exp_var "addressingModeDestination"))%exp)
                                                 | AND  => stm_call and_inst (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                               (_::_)
                                                                                                                               ((exp_var "BW"))%exp)
                                                                                                                     (_::_)
                                                                                                                     ((exp_var "sourceRegister"))%exp)
                                                                                                           (_::_)
                                                                                                           ((exp_var "addressingModeSource"))%exp)
                                                                                                 (_::_)
                                                                                                 ((exp_var "destinationRegister"))%exp)
                                                                                       (_::_)
                                                                                       ((exp_var "addressingModeDestination"))%exp)
                                                 | BIC  => stm_call bic_inst (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                               (_::_)
                                                                                                                               ((exp_var "BW"))%exp)
                                                                                                                     (_::_)
                                                                                                                     ((exp_var "sourceRegister"))%exp)
                                                                                                           (_::_)
                                                                                                           ((exp_var "addressingModeSource"))%exp)
                                                                                                 (_::_)
                                                                                                 ((exp_var "destinationRegister"))%exp)
                                                                                       (_::_)
                                                                                       ((exp_var "addressingModeDestination"))%exp)
                                                 | BIS  => stm_call bis_inst (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                               (_::_)
                                                                                                                               ((exp_var "BW"))%exp)
                                                                                                                     (_::_)
                                                                                                                     ((exp_var "sourceRegister"))%exp)
                                                                                                           (_::_)
                                                                                                           ((exp_var "addressingModeSource"))%exp)
                                                                                                 (_::_)
                                                                                                 ((exp_var "destinationRegister"))%exp)
                                                                                       (_::_)
                                                                                       ((exp_var "addressingModeDestination"))%exp)
                                                 | BIT  => stm_call bit_inst (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                               (_::_)
                                                                                                                               ((exp_var "BW"))%exp)
                                                                                                                     (_::_)
                                                                                                                     ((exp_var "sourceRegister"))%exp)
                                                                                                           (_::_)
                                                                                                           ((exp_var "addressingModeSource"))%exp)
                                                                                                 (_::_)
                                                                                                 ((exp_var "destinationRegister"))%exp)
                                                                                       (_::_)
                                                                                       ((exp_var "addressingModeDestination"))%exp)
                                                 | CMP  => stm_call cmp_inst (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                               (_::_)
                                                                                                                               ((exp_var "BW"))%exp)
                                                                                                                     (_::_)
                                                                                                                     ((exp_var "sourceRegister"))%exp)
                                                                                                           (_::_)
                                                                                                           ((exp_var "addressingModeSource"))%exp)
                                                                                                 (_::_)
                                                                                                 ((exp_var "destinationRegister"))%exp)
                                                                                       (_::_)
                                                                                       ((exp_var "addressingModeDestination"))%exp)
                                                 | DADD => stm_call dadd_inst (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                (_::_)
                                                                                                                                ((exp_var "BW"))%exp)
                                                                                                                      (_::_)
                                                                                                                      ((exp_var "sourceRegister"))%exp)
                                                                                                            (_::_)
                                                                                                            ((exp_var "addressingModeSource"))%exp)
                                                                                                  (_::_)
                                                                                                  ((exp_var "destinationRegister"))%exp)
                                                                                        (_::_)
                                                                                        ((exp_var "addressingModeDestination"))%exp)
                                                 | MOV  => stm_call move_inst (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                (_::_)
                                                                                                                                ((exp_var "BW"))%exp)
                                                                                                                      (_::_)
                                                                                                                      ((exp_var "sourceRegister"))%exp)
                                                                                                            (_::_)
                                                                                                            ((exp_var "addressingModeSource"))%exp)
                                                                                                  (_::_)
                                                                                                  ((exp_var "destinationRegister"))%exp)
                                                                                        (_::_)
                                                                                        ((exp_var "addressingModeDestination"))%exp)
                                                 | SUB  => stm_call sub_inst (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                               (_::_)
                                                                                                                               ((exp_var "BW"))%exp)
                                                                                                                     (_::_)
                                                                                                                     ((exp_var "sourceRegister"))%exp)
                                                                                                           (_::_)
                                                                                                           ((exp_var "addressingModeSource"))%exp)
                                                                                                 (_::_)
                                                                                                 ((exp_var "destinationRegister"))%exp)
                                                                                       (_::_)
                                                                                       ((exp_var "addressingModeDestination"))%exp)
                                                 | SUBC => stm_call subc_inst (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                (_::_)
                                                                                                                                ((exp_var "BW"))%exp)
                                                                                                                      (_::_)
                                                                                                                      ((exp_var "sourceRegister"))%exp)
                                                                                                            (_::_)
                                                                                                            ((exp_var "addressingModeSource"))%exp)
                                                                                                  (_::_)
                                                                                                  ((exp_var "destinationRegister"))%exp)
                                                                                        (_::_)
                                                                                        ((exp_var "addressingModeDestination"))%exp)
                                                 | XOR  => stm_call xor_inst (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                               (_::_)
                                                                                                                               ((exp_var "BW"))%exp)
                                                                                                                     (_::_)
                                                                                                                     ((exp_var "sourceRegister"))%exp)
                                                                                                           (_::_)
                                                                                                           ((exp_var "addressingModeSource"))%exp)
                                                                                                 (_::_)
                                                                                                 ((exp_var "destinationRegister"))%exp)
                                                                                       (_::_)
                                                                                       ((exp_var "addressingModeDestination"))%exp)
                                                 end))).
    
    (*
      Extended type
        parameter a
          ?[69:16]
        return value
          unit
      
      [0] : OCaml position: Pos(nanosail/SailToNanosail/Translate/ExtendedType.ml:230:7887:7914)
            Sail position: /nix/store/fv2f633qnl6cbj6fn0y9a1c1x0kmpish-ocaml5.2.1-sail-0.18/share/sail/lib/vector.sail:77
    *)
    Definition fun_execute_DOESNOTUNDERSTAND : Stm [
                                                     "a"  ∷  ty.bvec (16)
                                                   ]
                                                   (ty.unit) :=
      stm_seq (stm_exp (exp_union Uexception Kundefindedinstruction (exp_var "a")))
              (stm_fail _ "failure").
    
    (*
      Extended type
        parameter merge#var
          ast
        return value
          unit
    *)
    Definition fun_execute : Stm [
                                   "merge#var"  ∷  ty.union Uast
                                 ]
                                 (ty.unit) :=
      stm_let "ж4235"
              (ty.union Uast)
              (stm_exp (exp_var "merge#var"))
              (stm_match_union_alt_list Uast
                                        (stm_exp (exp_var "ж4235"))
                                        [
                                          existT Kdoesnotunderstand (MkAlt (pat_var "a") (stm_call execute_DOESNOTUNDERSTAND (env.snoc (env.nil)
                                                                                                                                       (_::_)
                                                                                                                                       ((exp_var "a"))%exp)));
                                          existT Kdoubleop (MkAlt (pat_tuple ("op", "BW", "sourceRegister", "addressingModeSource", "destinationRegister", "addressingModeDestination")) (stm_call execute_DOUBLEOP (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                                                                                                                (_::_)
                                                                                                                                                                                                                                                                                ((exp_var "op"))%exp)
                                                                                                                                                                                                                                                                      (_::_)
                                                                                                                                                                                                                                                                      ((exp_var "BW"))%exp)
                                                                                                                                                                                                                                                            (_::_)
                                                                                                                                                                                                                                                            ((exp_var "sourceRegister"))%exp)
                                                                                                                                                                                                                                                  (_::_)
                                                                                                                                                                                                                                                  ((exp_var "addressingModeSource"))%exp)
                                                                                                                                                                                                                                        (_::_)
                                                                                                                                                                                                                                        ((exp_var "destinationRegister"))%exp)
                                                                                                                                                                                                                              (_::_)
                                                                                                                                                                                                                              ((exp_var "addressingModeDestination"))%exp)));
                                          existT Kjump (MkAlt (pat_pair "op" "offset") (stm_call execute_JUMP (env.snoc (env.snoc (env.nil)
                                                                                                                                  (_::_)
                                                                                                                                  ((exp_var "op"))%exp)
                                                                                                                        (_::_)
                                                                                                                        ((exp_var "offset"))%exp)));
                                          existT Ksingleop (MkAlt (pat_tuple ("op", "BW", "addressingMode", "reg")) (stm_call execute_SINGLEOP (env.snoc (env.snoc (env.snoc (env.snoc (env.nil)
                                                                                                                                                                                       (_::_)
                                                                                                                                                                                       ((exp_var "op"))%exp)
                                                                                                                                                                             (_::_)
                                                                                                                                                                             ((exp_var "BW"))%exp)
                                                                                                                                                                   (_::_)
                                                                                                                                                                   ((exp_var "addressingMode"))%exp)
                                                                                                                                                         (_::_)
                                                                                                                                                         ((exp_var "reg"))%exp)))
                                        ]
                                        Logic.I).
    
    (*
      Extended type
        parameter _ж4254
          unit
        return value
          unit
    *)
    Definition fun_initialize_registers : Stm [
                                                "_ж4254"  ∷  ty.unit
                                              ]
                                              (ty.unit) :=
      stm_seq (stm_seq (stm_let "ж4255"
                                (ty.bvec (64))
                                (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                        (_::_)
                                                                        ((exp_int 64%Z))%exp))
                                (stm_write_register verbosity (exp_var "ж4255")))
                       (stm_exp (exp_val (ty.unit) (tt))))
              (stm_seq (stm_seq (stm_let "ж4257"
                                         (ty.wordBits)
                                         (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                 (_::_)
                                                                                 ((exp_int 16%Z))%exp))
                                         (stm_write_register old_PC_reg (exp_var "ж4257")))
                                (stm_exp (exp_val (ty.unit) (tt))))
                       (stm_seq (stm_seq (stm_let "ж4259"
                                                  (ty.wordBits)
                                                  (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                          (_::_)
                                                                                          ((exp_int 16%Z))%exp))
                                                  (stm_write_register PC_reg (exp_var "ж4259")))
                                         (stm_exp (exp_val (ty.unit) (tt))))
                                (stm_seq (stm_seq (stm_let "ж4261"
                                                           (ty.wordBits)
                                                           (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                   (_::_)
                                                                                                   ((exp_int 16%Z))%exp))
                                                           (stm_write_register SP_reg (exp_var "ж4261")))
                                                  (stm_exp (exp_val (ty.unit) (tt))))
                                         (stm_seq (stm_seq (stm_let "ж4263"
                                                                    (ty.wordBits)
                                                                    (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                            (_::_)
                                                                                                            ((exp_int 16%Z))%exp))
                                                                    (stm_write_register SRCG1_reg (exp_var "ж4263")))
                                                           (stm_exp (exp_val (ty.unit) (tt))))
                                                  (stm_seq (stm_seq (stm_let "ж4265"
                                                                             (ty.wordBits)
                                                                             (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                     (_::_)
                                                                                                                     ((exp_int 16%Z))%exp))
                                                                             (stm_write_register CG2_reg (exp_var "ж4265")))
                                                                    (stm_exp (exp_val (ty.unit) (tt))))
                                                           (stm_seq (stm_seq (stm_let "ж4267"
                                                                                      (ty.wordBits)
                                                                                      (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                              (_::_)
                                                                                                                              ((exp_int 16%Z))%exp))
                                                                                      (stm_write_register R4_reg (exp_var "ж4267")))
                                                                             (stm_exp (exp_val (ty.unit) (tt))))
                                                                    (stm_seq (stm_seq (stm_let "ж4269"
                                                                                               (ty.wordBits)
                                                                                               (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                       (_::_)
                                                                                                                                       ((exp_int 16%Z))%exp))
                                                                                               (stm_write_register R5_reg (exp_var "ж4269")))
                                                                                      (stm_exp (exp_val (ty.unit) (tt))))
                                                                             (stm_seq (stm_seq (stm_let "ж4271"
                                                                                                        (ty.wordBits)
                                                                                                        (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                (_::_)
                                                                                                                                                ((exp_int 16%Z))%exp))
                                                                                                        (stm_write_register R6_reg (exp_var "ж4271")))
                                                                                               (stm_exp (exp_val (ty.unit) (tt))))
                                                                                      (stm_seq (stm_seq (stm_let "ж4273"
                                                                                                                 (ty.wordBits)
                                                                                                                 (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                         (_::_)
                                                                                                                                                         ((exp_int 16%Z))%exp))
                                                                                                                 (stm_write_register R7_reg (exp_var "ж4273")))
                                                                                                        (stm_exp (exp_val (ty.unit) (tt))))
                                                                                               (stm_seq (stm_seq (stm_let "ж4275"
                                                                                                                          (ty.wordBits)
                                                                                                                          (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                  (_::_)
                                                                                                                                                                  ((exp_int 16%Z))%exp))
                                                                                                                          (stm_write_register R8_reg (exp_var "ж4275")))
                                                                                                                 (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                        (stm_seq (stm_seq (stm_let "ж4277"
                                                                                                                                   (ty.wordBits)
                                                                                                                                   (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                           (_::_)
                                                                                                                                                                           ((exp_int 16%Z))%exp))
                                                                                                                                   (stm_write_register R9_reg (exp_var "ж4277")))
                                                                                                                          (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                 (stm_seq (stm_seq (stm_let "ж4279"
                                                                                                                                            (ty.wordBits)
                                                                                                                                            (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                                    (_::_)
                                                                                                                                                                                    ((exp_int 16%Z))%exp))
                                                                                                                                            (stm_write_register R10_reg (exp_var "ж4279")))
                                                                                                                                   (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                          (stm_seq (stm_seq (stm_let "ж4281"
                                                                                                                                                     (ty.wordBits)
                                                                                                                                                     (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                                             (_::_)
                                                                                                                                                                                             ((exp_int 16%Z))%exp))
                                                                                                                                                     (stm_write_register R11_reg (exp_var "ж4281")))
                                                                                                                                            (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                                   (stm_seq (stm_seq (stm_let "ж4283"
                                                                                                                                                              (ty.wordBits)
                                                                                                                                                              (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                                                      (_::_)
                                                                                                                                                                                                      ((exp_int 16%Z))%exp))
                                                                                                                                                              (stm_write_register R12_reg (exp_var "ж4283")))
                                                                                                                                                     (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                                            (stm_seq (stm_seq (stm_let "ж4285"
                                                                                                                                                                       (ty.wordBits)
                                                                                                                                                                       (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                                                               (_::_)
                                                                                                                                                                                                               ((exp_int 16%Z))%exp))
                                                                                                                                                                       (stm_write_register R13_reg (exp_var "ж4285")))
                                                                                                                                                              (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                                                     (stm_seq (stm_seq (stm_let "ж4287"
                                                                                                                                                                                (ty.wordBits)
                                                                                                                                                                                (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                                                                        (_::_)
                                                                                                                                                                                                                        ((exp_int 16%Z))%exp))
                                                                                                                                                                                (stm_write_register R14_reg (exp_var "ж4287")))
                                                                                                                                                                       (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                                                              (stm_seq (stm_seq (stm_let "ж4289"
                                                                                                                                                                                         (ty.wordBits)
                                                                                                                                                                                         (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                                                                                 (_::_)
                                                                                                                                                                                                                                 ((exp_int 16%Z))%exp))
                                                                                                                                                                                         (stm_write_register R15_reg (exp_var "ж4289")))
                                                                                                                                                                                (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                                                                       (stm_seq (stm_seq (stm_let "ж4291"
                                                                                                                                                                                                  (ty.wordBits)
                                                                                                                                                                                                  (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                                                                                          (_::_)
                                                                                                                                                                                                                                          ((exp_int 16%Z))%exp))
                                                                                                                                                                                                  (stm_write_register MPUCTL0_reg (exp_var "ж4291")))
                                                                                                                                                                                         (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                                                                                (stm_seq (stm_seq (stm_let "ж4293"
                                                                                                                                                                                                           (ty.wordBits)
                                                                                                                                                                                                           (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                                                                                                   (_::_)
                                                                                                                                                                                                                                                   ((exp_int 16%Z))%exp))
                                                                                                                                                                                                           (stm_write_register MPUCTL1_reg (exp_var "ж4293")))
                                                                                                                                                                                                  (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                                                                                         (stm_seq (stm_seq (stm_let "ж4295"
                                                                                                                                                                                                                    (ty.wordBits)
                                                                                                                                                                                                                    (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                                                                                                            (_::_)
                                                                                                                                                                                                                                                            ((exp_int 16%Z))%exp))
                                                                                                                                                                                                                    (stm_write_register MPUSEGB2_reg (exp_var "ж4295")))
                                                                                                                                                                                                           (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                                                                                                  (stm_seq (stm_seq (stm_let "ж4297"
                                                                                                                                                                                                                             (ty.wordBits)
                                                                                                                                                                                                                             (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                                                                                                                     (_::_)
                                                                                                                                                                                                                                                                     ((exp_int 16%Z))%exp))
                                                                                                                                                                                                                             (stm_write_register MPUSEGB1_reg (exp_var "ж4297")))
                                                                                                                                                                                                                    (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                                                                                                           (stm_seq (stm_seq (stm_let "ж4299"
                                                                                                                                                                                                                                      (ty.wordBits)
                                                                                                                                                                                                                                      (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                                                                                                                              (_::_)
                                                                                                                                                                                                                                                                              ((exp_int 16%Z))%exp))
                                                                                                                                                                                                                                      (stm_write_register MPUSAM_reg (exp_var "ж4299")))
                                                                                                                                                                                                                             (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                                                                                                                    (stm_seq (stm_seq (stm_let "ж4301"
                                                                                                                                                                                                                                               (ty.wordBits)
                                                                                                                                                                                                                                               (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                                                                                                                                       (_::_)
                                                                                                                                                                                                                                                                                       ((exp_int 16%Z))%exp))
                                                                                                                                                                                                                                               (stm_write_register MPUIPC0_reg (exp_var "ж4301")))
                                                                                                                                                                                                                                      (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                                                                                                                             (stm_seq (stm_seq (stm_let "ж4303"
                                                                                                                                                                                                                                                        (ty.wordBits)
                                                                                                                                                                                                                                                        (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                                                                                                                                                (_::_)
                                                                                                                                                                                                                                                                                                ((exp_int 16%Z))%exp))
                                                                                                                                                                                                                                                        (stm_write_register MPUIPSEGB2_reg (exp_var "ж4303")))
                                                                                                                                                                                                                                               (stm_exp (exp_val (ty.unit) (tt))))
                                                                                                                                                                                                                                      (stm_seq (stm_let "ж4305"
                                                                                                                                                                                                                                                        (ty.wordBits)
                                                                                                                                                                                                                                                        (stm_call undefined_bitvector (env.snoc (env.nil)
                                                                                                                                                                                                                                                                                                (_::_)
                                                                                                                                                                                                                                                                                                ((exp_int 16%Z))%exp))
                                                                                                                                                                                                                                                        (stm_write_register MPUIPSEGB1_reg (exp_var "ж4305")))
                                                                                                                                                                                                                                               (stm_exp (exp_val (ty.unit) (tt)))))))))))))))))))))))))))).

    Definition undefined_function {Δ τ} : Stm Δ τ :=
      stm_fail _ "".

    Definition FunDef {Δ}
                      {τ}
                      (f : Fun Δ τ) : Stm Δ τ :=
      match f in Fun Δ τ return Stm Δ τ with
      | neg_vec4                             => fun_neg_vec4
      | bitmaping_forwards                   => fun_bitmaping_forwards
      | bitmaping_backwards                  => fun_bitmaping_backwards
      | bitmaping_forwards_matches           => fun_bitmaping_forwards_matches
      | bitmaping_backwards_matches          => fun_bitmaping_backwards_matches
      | regName                              => fun_regName
      | AMstring                             => fun_AMstring
      | BWstring                             => fun_BWstring
      | BWSizeString                         => fun_BWSizeString
      | duopName                             => fun_duopName
      | singleopName                         => fun_singleopName
      | jumpName                             => fun_jumpName
      | logWithVerbosity                     => fun_logWithVerbosity
      | RegisterMapping_forwards             => fun_RegisterMapping_forwards
      | RegisterMapping_backwards            => fun_RegisterMapping_backwards
      | RegisterMapping_forwards_matches     => fun_RegisterMapping_forwards_matches
      | RegisterMapping_backwards_matches    => fun_RegisterMapping_backwards_matches
      | init_base_regs                       => fun_init_base_regs
      | toByte                               => fun_toByte
      | signedWb                             => fun_signedWb
      | unsignedWb                           => fun_unsignedWb
      | addBw                                => fun_addBw
      | zero_extend_bit_to_byte              => fun_zero_extend_bit_to_byte
      | not_wordByte                         => fun_not_wordByte
      | and_wordByte                         => fun_and_wordByte
      | or_wordByte                          => fun_or_wordByte
      | xor_wordByte                         => fun_xor_wordByte
      | eq_wordByte                          => fun_eq_wordByte
      | xor_bool                             => fun_xor_bool
      | isNegative                           => fun_isNegative
      | isZero                               => fun_isZero
      | printWordByte                        => fun_printWordByte
      | WordByteString                       => fun_WordByteString
      | getOverflowBit                       => fun_getOverflowBit
      | setOverflowbitBit                    => fun_setOverflowbitBit
      | setOverflowbitTrue                   => fun_setOverflowbitTrue
      | clearOverflowbit                     => fun_clearOverflowbit
      | overflowbitSet                       => fun_overflowbitSet
      | getNegativeBit                       => fun_getNegativeBit
      | setNegativebitBit                    => fun_setNegativebitBit
      | setNegativebitTrue                   => fun_setNegativebitTrue
      | clearNegativebit                     => fun_clearNegativebit
      | negativebitSet                       => fun_negativebitSet
      | getZeroBit                           => fun_getZeroBit
      | setZerobitBit                        => fun_setZerobitBit
      | setZerobitTrue                       => fun_setZerobitTrue
      | clearZerobit                         => fun_clearZerobit
      | zerobitSet                           => fun_zerobitSet
      | getCarryBit                          => fun_getCarryBit
      | setCarrybitBit                       => fun_setCarrybitBit
      | setCarrybitTrue                      => fun_setCarrybitTrue
      | clearCarrybit                        => fun_clearCarrybit
      | carrybitSet                          => fun_carrybitSet
      | setAllStatusbits                     => fun_setAllStatusbits
      | clearStatusRegisters                 => fun_clearStatusRegisters
      | setResultStatusRegisters             => fun_setResultStatusRegisters
      | mpu_register_index_forwards          => fun_mpu_register_index_forwards
      | mpu_register_index_backwards         => fun_mpu_register_index_backwards
      | mpu_register_index_forwards_matches  => fun_mpu_register_index_forwards_matches
      | mpu_register_index_backwards_matches => fun_mpu_register_index_backwards_matches
      | is_mpu_reg_addr                      => fun_is_mpu_reg_addr
      | read_mpu_reg_byte                    => fun_read_mpu_reg_byte
      | is_lockable_mpu_reg                  => fun_is_lockable_mpu_reg
      | is_ipe_reg                           => fun_is_ipe_reg
      | write_mpu_reg_byte                   => fun_write_mpu_reg_byte
      | ipe_lower                            => fun_ipe_lower
      | ipe_higher                           => fun_ipe_higher
      | in_ipe_segment                       => fun_in_ipe_segment
      | in_ivt_or_rv                         => fun_in_ivt_or_rv
      | is_x                                 => fun_is_x
      | check_ipe_access                     => fun_check_ipe_access
      | check_byte_access                    => fun_check_byte_access
      | read_mem_aux                         => fun_read_mem_aux
      | readMem                              => fun_readMem
      | writeMem                             => fun_writeMem
      | readMemInstruction                   => fun_readMemInstruction
      | writeMemInstruction                  => fun_writeMemInstruction
      | incPC                                => fun_incPC
      | fetch                                => fun_fetch
      | sourcemaping_forwards                => fun_sourcemaping_forwards
      | sourcemaping_backwards               => fun_sourcemaping_backwards
      | sourcemaping_forwards_matches        => fun_sourcemaping_forwards_matches
      | sourcemaping_backwards_matches       => fun_sourcemaping_backwards_matches
      | destinationmaping_forwards           => fun_destinationmaping_forwards
      | destinationmaping_backwards          => fun_destinationmaping_backwards
      | destinationmaping_forwards_matches   => fun_destinationmaping_forwards_matches
      | destinationmaping_backwards_matches  => fun_destinationmaping_backwards_matches
      | readReg                              => fun_readReg
      | writeReg                             => fun_writeReg
      | read                                 => fun_read
      | write                                => fun_write
      | move_inst                            => fun_move_inst
      | hasCarry                             => fun_hasCarry
      | hasOverflowAddition                  => fun_hasOverflowAddition
      | addWithStatusRegister                => fun_addWithStatusRegister
      | add_inst                             => fun_add_inst
      | addc_inst                            => fun_addc_inst
      | sub_inst                             => fun_sub_inst
      | subc_inst                            => fun_subc_inst
      | cmp_inst                             => fun_cmp_inst
      | andWithStatusRegister                => fun_andWithStatusRegister
      | and_inst                             => fun_and_inst
      | xorWithStatusRegister                => fun_xorWithStatusRegister
      | xor_inst                             => fun_xor_inst
      | bic_inst                             => fun_bic_inst
      | bis_inst                             => fun_bis_inst
      | bit_inst                             => fun_bit_inst
      | asDecimal                            => fun_asDecimal
      | asWordByte                           => fun_asWordByte
      | dadd_inst                            => fun_dadd_inst
      | encdec_doubleop_forwards             => fun_encdec_doubleop_forwards
      | encdec_doubleop_backwards            => fun_encdec_doubleop_backwards
      | encdec_doubleop_forwards_matches     => fun_encdec_doubleop_forwards_matches
      | encdec_doubleop_backwards_matches    => fun_encdec_doubleop_backwards_matches
      | rrc_inst                             => fun_rrc_inst
      | rra_inst                             => fun_rra_inst
      | push_inst                            => fun_push_inst
      | swpb_inst                            => fun_swpb_inst
      | call_inst                            => fun_call_inst
      | reti_inst                            => fun_reti_inst
      | sxt_inst                             => fun_sxt_inst
      | encdec_singleop_forwards             => fun_encdec_singleop_forwards
      | encdec_singleop_backwards            => fun_encdec_singleop_backwards
      | encdec_singleop_forwards_matches     => fun_encdec_singleop_forwards_matches
      | encdec_singleop_backwards_matches    => fun_encdec_singleop_backwards_matches
      | jeq_inst                             => fun_jeq_inst
      | jne_inst                             => fun_jne_inst
      | jc_inst                              => fun_jc_inst
      | jnc_inst                             => fun_jnc_inst
      | jn_inst                              => fun_jn_inst
      | jge_inst                             => fun_jge_inst
      | jl_inst                              => fun_jl_inst
      | jmp_inst                             => fun_jmp_inst
      | encdec_jump_forwards                 => fun_encdec_jump_forwards
      | encdec_jump_backwards                => fun_encdec_jump_backwards
      | encdec_jump_forwards_matches         => fun_encdec_jump_forwards_matches
      | encdec_jump_backwards_matches        => fun_encdec_jump_backwards_matches
      | formatAst                            => fun_formatAst
      | encdec_forwards                      => fun_encdec_forwards
      | encdec_forwards_matches              => fun_encdec_forwards_matches
      | execute_SINGLEOP                     => fun_execute_SINGLEOP
      | execute_JUMP                         => fun_execute_JUMP
      | execute_DOUBLEOP                     => fun_execute_DOUBLEOP
      | execute_DOESNOTUNDERSTAND            => fun_execute_DOESNOTUNDERSTAND
      | execute                              => fun_execute
      | initialize_registers                 => fun_initialize_registers
      | _                                    => undefined_function
      end.
  End FunDefKit.
  
  Include DefaultRegStoreKit UntitledBase.
  
  Section ForeignKit.
    Definition ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs)
      (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory) : Prop := False.
    Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
      exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
    Proof. destruct f. Qed.
  End ForeignKit.
  
  Include ProgramMixin UntitledBase.
End ModelProgram.
