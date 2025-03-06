From Coq Require Import Classes.EquivDec
                        Strings.String
                        ZArith.

From stdpp Require finite.

From Equations Require Import Equations.

From Katamaran Require Import Base
                              Bitvector.

(*
  Registers' initial values
  
  verbosity
    <no initial value specified>
  old_PC_reg
    <no initial value specified>
  PC_reg
    <no initial value specified>
  SP_reg
    <no initial value specified>
  SRCG1_reg
    <no initial value specified>
  CG2_reg
    <no initial value specified>
  R4_reg
    <no initial value specified>
  R5_reg
    <no initial value specified>
  R6_reg
    <no initial value specified>
  R7_reg
    <no initial value specified>
  R8_reg
    <no initial value specified>
  R9_reg
    <no initial value specified>
  R10_reg
    <no initial value specified>
  R11_reg
    <no initial value specified>
  R12_reg
    <no initial value specified>
  R13_reg
    <no initial value specified>
  R14_reg
    <no initial value specified>
  R15_reg
    <no initial value specified>
  MPUCTL0_reg
    <no initial value specified>
  MPUCTL1_reg
    <no initial value specified>
  MPUSEGB2_reg
    <no initial value specified>
  MPUSEGB1_reg
    <no initial value specified>
  MPUSAM_reg
    <no initial value specified>
  MPUIPC0_reg
    <no initial value specified>
  MPUIPSEGB2_reg
    <no initial value specified>
  MPUIPSEGB1_reg
    <no initial value specified>
  LastInstructionFetch
    <raw> Word(undefined_bitvector(16))
*)
Inductive RegName : Set :=
  | RegName_verbosity           
  | RegName_old_PC_reg          
  | RegName_PC_reg              
  | RegName_SP_reg              
  | RegName_SRCG1_reg           
  | RegName_CG2_reg             
  | RegName_R4_reg              
  | RegName_R5_reg              
  | RegName_R6_reg              
  | RegName_R7_reg              
  | RegName_R8_reg              
  | RegName_R9_reg              
  | RegName_R10_reg             
  | RegName_R11_reg             
  | RegName_R12_reg             
  | RegName_R13_reg             
  | RegName_R14_reg             
  | RegName_R15_reg             
  | RegName_MPUCTL0_reg         
  | RegName_MPUCTL1_reg         
  | RegName_MPUSEGB2_reg        
  | RegName_MPUSEGB1_reg        
  | RegName_MPUSAM_reg          
  | RegName_MPUIPC0_reg         
  | RegName_MPUIPSEGB2_reg      
  | RegName_MPUIPSEGB1_reg      
  | RegName_LastInstructionFetch.

Inductive exception : Set :=
  | notImplemented        : String.string -> exception
  | notAllowed            : String.string -> exception
  | undefindedBehavior    : String.string -> exception
  | undefindedInstruction : bv 16 -> exception
  | ipe_violation         : bv 16 -> exception
  | power_up_clear        : exception
  | test_fail             : String.string -> exception.

Inductive exceptionConstructor : Set :=
  | Knotimplemented       
  | Knotallowed           
  | Kundefindedbehavior   
  | Kundefindedinstruction
  | Kipe_violation        
  | Kpower_up_clear       
  | Ktest_fail            .

Definition len_word :=
  16.

Definition len_byte :=
  8.

Definition wordBits :=
  bv 16.

Definition byteBits :=
  bv 8.

Inductive BW : Set :=
  | WORD_INSTRUCTION
  | BYTE_INSTRUCTION.

Inductive WordByte : Set :=
  | Byte : byteBits -> WordByte
  | Word : wordBits -> WordByte.

Inductive WordByteConstructor : Set :=
  | Kbyte
  | Kword.

Definition registerAddressLen :=
  4.

Definition registerAddressBits :=
  bv 4.

Definition address_size :=
  16.

Definition Address :=
  bv 16.

Definition addressingModeSourceLen :=
  2.

Definition addressingModeSourceBits :=
  bv 2.

Definition addressingModeDestinationLen :=
  1.

Definition addressingModeDestinationBits :=
  bv 1.

Inductive Register : Set :=
  | PC   
  | SP   
  | SRCG1
  | CG2  
  | R4   
  | R5   
  | R6   
  | R7   
  | R8   
  | R9   
  | R10  
  | R11  
  | R12  
  | R13  
  | R14  
  | R15  .

Inductive AM : Set :=
  | REGISTER_MODE              
  | INDEXED_MODE               
  | INDIRECT_REGISTER_MODE     
  | INDIRECT_AUTOINCREMENT_MODE.

Inductive doubleop : Set :=
  | MOV 
  | ADD 
  | ADDC
  | SUB 
  | SUBC
  | CMP 
  | DADD
  | BIT 
  | BIC 
  | BIS 
  | XOR 
  | AND .

Inductive singleop : Set :=
  | RRC 
  | RRA 
  | PUSH
  | SWPB
  | CALL
  | RETI
  | SXT .

Inductive jump : Set :=
  | JEQ
  | JNE
  | JC 
  | JNC
  | JN 
  | JGE
  | JL 
  | JMP.

Inductive mpu_register_name : Set :=
  | MPUCTL0   
  | MPUCTL1   
  | MPUSEGB2  
  | MPUSEGB1  
  | MPUSAM    
  | MPUIPC0   
  | MPUIPSEGB2
  | MPUIPSEGB1.

Inductive access_mode : Set :=
  | R
  | W
  | X.

Inductive ast : Set :=
  | DOUBLEOP          : doubleop -> BW -> Register -> AM -> Register -> AM -> ast
  | SINGLEOP          : singleop -> BW -> AM -> Register -> ast
  | JUMP              : jump -> bv 10 -> ast
  | DOESNOTUNDERSTAND : bv 16 -> ast.

Inductive astConstructor : Set :=
  | Kdoubleop         
  | Ksingleop         
  | Kjump             
  | Kdoesnotunderstand.

Definition OffsetLen :=
  10.

Definition Offset :=
  bv 10.

Inductive Enums : Set :=
  | regname           
  | Ebw               
  | Eregister         
  | Eam               
  | Edoubleop         
  | Esingleop         
  | Ejump             
  | Empu_register_name
  | Eaccess_mode      .

Inductive Unions : Set :=
  | Uexception
  | Uwordbyte 
  | Uast      .

Inductive Records : Set :=.

Section TransparentObligations.
  Local Set Transparent Obligations.
  
  Derive NoConfusion for exception.
  Derive NoConfusion for exceptionConstructor.
  Derive NoConfusion for BW.
  Derive NoConfusion for WordByte.
  Derive NoConfusion for WordByteConstructor.
  Derive NoConfusion for Register.
  Derive NoConfusion for AM.
  Derive NoConfusion for doubleop.
  Derive NoConfusion for singleop.
  Derive NoConfusion for jump.
  Derive NoConfusion for mpu_register_name.
  Derive NoConfusion for access_mode.
  Derive NoConfusion for ast.
  Derive NoConfusion for astConstructor.
  Derive NoConfusion for Enums.
  Derive NoConfusion for Unions.
  Derive NoConfusion for Records.
  Derive NoConfusion for RegName.
End TransparentObligations.

Derive EqDec for exception.
Derive EqDec for exceptionConstructor.
Derive EqDec for BW.
Derive EqDec for WordByte.
Derive EqDec for WordByteConstructor.
Derive EqDec for Register.
Derive EqDec for AM.
Derive EqDec for doubleop.
Derive EqDec for singleop.
Derive EqDec for jump.
Derive EqDec for mpu_register_name.
Derive EqDec for access_mode.
Derive EqDec for ast.
Derive EqDec for astConstructor.
Derive EqDec for Enums.
Derive EqDec for Unions.
Derive EqDec for Records.
Derive EqDec for RegName.

Section Finite.
  Import stdpp.finite.
  
  Local Obligation Tactic :=
    finite_from_eqdec.
  
  #[export,program] Instance BW_finite : Finite BW :=
    {|enum:=[
              WORD_INSTRUCTION;
              BYTE_INSTRUCTION
            ]|}.
  
  #[export,program] Instance Register_finite : Finite Register :=
    {|enum:=[
              PC;
              SP;
              SRCG1;
              CG2;
              R4;
              R5;
              R6;
              R7;
              R8;
              R9;
              R10;
              R11;
              R12;
              R13;
              R14;
              R15
            ]|}.
  
  #[export,program] Instance AM_finite : Finite AM :=
    {|enum:=[
              REGISTER_MODE;
              INDEXED_MODE;
              INDIRECT_REGISTER_MODE;
              INDIRECT_AUTOINCREMENT_MODE
            ]|}.
  
  #[export,program] Instance doubleop_finite : Finite doubleop :=
    {|enum:=[
              MOV;
              ADD;
              ADDC;
              SUB;
              SUBC;
              CMP;
              DADD;
              BIT;
              BIC;
              BIS;
              XOR;
              AND
            ]|}.
  
  #[export,program] Instance singleop_finite : Finite singleop :=
    {|enum:=[
              RRC;
              RRA;
              PUSH;
              SWPB;
              CALL;
              RETI;
              SXT
            ]|}.
  
  #[export,program] Instance jump_finite : Finite jump :=
    {|enum:=[
              JEQ;
              JNE;
              JC;
              JNC;
              JN;
              JGE;
              JL;
              JMP
            ]|}.
  
  #[export,program] Instance mpu_register_name_finite : Finite mpu_register_name :=
    {|enum:=[
              MPUCTL0;
              MPUCTL1;
              MPUSEGB2;
              MPUSEGB1;
              MPUSAM;
              MPUIPC0;
              MPUIPSEGB2;
              MPUIPSEGB1
            ]|}.
  
  #[export,program] Instance access_mode_finite : Finite access_mode :=
    {|enum:=[
              R;
              W;
              X
            ]|}.
  
  #[export,program] Instance RegName_finite : Finite RegName :=
    {|enum:=[
              RegName_verbosity;
              RegName_old_PC_reg;
              RegName_PC_reg;
              RegName_SP_reg;
              RegName_SRCG1_reg;
              RegName_CG2_reg;
              RegName_R4_reg;
              RegName_R5_reg;
              RegName_R6_reg;
              RegName_R7_reg;
              RegName_R8_reg;
              RegName_R9_reg;
              RegName_R10_reg;
              RegName_R11_reg;
              RegName_R12_reg;
              RegName_R13_reg;
              RegName_R14_reg;
              RegName_R15_reg;
              RegName_MPUCTL0_reg;
              RegName_MPUCTL1_reg;
              RegName_MPUSEGB2_reg;
              RegName_MPUSEGB1_reg;
              RegName_MPUSAM_reg;
              RegName_MPUIPC0_reg;
              RegName_MPUIPSEGB2_reg;
              RegName_MPUIPSEGB1_reg;
              RegName_LastInstructionFetch
            ]|}.
  
  #[export,program] Instance exceptionConstructor_finite : Finite exceptionConstructor :=
    {|enum:=[
              Knotimplemented;
              Knotallowed;
              Kundefindedbehavior;
              Kundefindedinstruction;
              Kipe_violation;
              Kpower_up_clear;
              Ktest_fail
            ]|}.
  
  #[export,program] Instance WordByteConstructor_finite : Finite WordByteConstructor :=
    {|enum:=[
              Kbyte;
              Kword
            ]|}.
  
  #[export,program] Instance astConstructor_finite : Finite astConstructor :=
    {|enum:=[
              Kdoubleop;
              Ksingleop;
              Kjump;
              Kdoesnotunderstand
            ]|}.
End Finite.

Module Export UntitledBase <: Base.
  Import ctx.notations.
  Import ctx.resolution.
  Import env.notations.
  Import stdpp.finite.
  
  Local Open Scope string_scope.
  
  Notation "'ty.wordBits'" := (ty.bvec (16)).
  Notation "'ty.byteBits'" := (ty.bvec (8)).
  Notation "'ty.registerAddressBits'" := (ty.bvec (4)).
  Notation "'ty.Address'" := (ty.bvec (16)).
  Notation "'ty.addressingModeSourceBits'" := (ty.bvec (2)).
  Notation "'ty.addressingModeDestinationBits'" := (ty.bvec (1)).
  Notation "'ty.Offset'" := (ty.bvec (10)).
  
  #[export] Instance typedeclkit : TypeDeclKit :=
    {|
       enumi   := Enums;
       unioni  := Unions;
       recordi := Records;
    |}.
  
  Definition enum_denote (e : Enums) : Set :=
    match e with
    | regname            => RegName
    | Ebw                => BW
    | Eregister          => Register
    | Eam                => AM
    | Edoubleop          => doubleop
    | Esingleop          => singleop
    | Ejump              => jump
    | Empu_register_name => mpu_register_name
    | Eaccess_mode       => access_mode
    end.
  
  Definition union_denote (u : Unions) : Set :=
    match u with
    | Uexception => exception
    | Uwordbyte  => WordByte
    | Uast       => ast
    end.
  
  Definition record_denote (r : Records) : Set :=
    match r with
    end.
  
  #[export] Instance typedenotekit : TypeDenoteKit typedeclkit :=
    {|
       enumt := enum_denote;
       uniont := union_denote;
       recordt := record_denote;
    |}.
  
  Definition union_constructor (u : Unions) : Set :=
    match u with
    | Uexception => exceptionConstructor
    | Uwordbyte  => WordByteConstructor
    | Uast       => astConstructor
    end.
  
  Definition union_constructor_type (u : Unions) : union_constructor u -> Ty :=
    match u with
    | Uexception => fun k => match k with
                             | Knotimplemented        => ty.string
                             | Knotallowed            => ty.string
                             | Kundefindedbehavior    => ty.string
                             | Kundefindedinstruction => ty.bvec (16)
                             | Kipe_violation         => ty.bvec (16)
                             | Kpower_up_clear        => ty.unit
                             | Ktest_fail             => ty.string
                             end
    | Uwordbyte  => fun k => match k with
                             | Kbyte => ty.byteBits
                             | Kword => ty.wordBits
                             end
    | Uast       => fun k => match k with
                             | Kdoubleop          => ty.tuple [
                                                                ty.enum Edoubleop;
                                                                ty.enum Ebw;
                                                                ty.enum Eregister;
                                                                ty.enum Eam;
                                                                ty.enum Eregister;
                                                                ty.enum Eam
                                                              ]
                             | Ksingleop          => ty.tuple [
                                                                ty.enum Esingleop;
                                                                ty.enum Ebw;
                                                                ty.enum Eam;
                                                                ty.enum Eregister
                                                              ]
                             | Kjump              => ty.prod (ty.enum Ejump) (ty.bvec (10))
                             | Kdoesnotunderstand => ty.bvec (16)
                             end
    end.
  
  #[export] Instance eqdec_enum_denote E : EqDec (enum_denote E) :=
    ltac:(destruct E; auto with typeclass_instances).
  #[export] Instance finite_enum_denote E : finite.Finite (enum_denote E) :=
    ltac:(destruct E; auto with typeclass_instances).
  #[export] Instance eqdec_union_denote U : EqDec (union_denote U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance eqdec_union_constructor U : EqDec (union_constructor U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance finite_union_constructor U : finite.Finite (union_constructor U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  #[export] Instance eqdec_record_denote R : EqDec (record_denote R) :=
    ltac:(destruct R; auto with typeclass_instances).
  
  Definition union_fold (U : unioni) : { K & Val (union_constructor_type U K) } -> uniont U :=
    match U with
    | Uexception => fun Kv => match Kv with
                              | existT Knotimplemented ж1        => notImplemented ж1
                              | existT Knotallowed ж1            => notAllowed ж1
                              | existT Kundefindedbehavior ж1    => undefindedBehavior ж1
                              | existT Kundefindedinstruction ж1 => undefindedInstruction ж1
                              | existT Kipe_violation ж1         => ipe_violation ж1
                              | existT Kpower_up_clear tt         => power_up_clear
                              | existT Ktest_fail ж1             => test_fail ж1
                              end
    | Uwordbyte  => fun Kv => match Kv with
                              | existT Kbyte ж1 => Byte ж1
                              | existT Kword ж1 => Word ж1
                              end
    | Uast       => fun Kv => match Kv with
                              | existT Kdoubleop (tt, ж1, ж2, ж3, ж4, ж5, ж6) => DOUBLEOP ж1 ж2 ж3 ж4 ж5 ж6
                              | existT Ksingleop (tt, ж1, ж2, ж3, ж4)           => SINGLEOP ж1 ж2 ж3 ж4
                              | existT Kjump (ж1, ж2)                             => JUMP ж1 ж2
                              | existT Kdoesnotunderstand ж1                       => DOESNOTUNDERSTAND ж1
                              end
    end.
  
  Definition union_unfold (U : unioni) : uniont U -> { K & Val (union_constructor_type U K) } :=
    match U with
    | Uexception => fun Kv => match Kv with
                              | notImplemented ж1        => existT Knotimplemented ж1
                              | notAllowed ж1            => existT Knotallowed ж1
                              | undefindedBehavior ж1    => existT Kundefindedbehavior ж1
                              | undefindedInstruction ж1 => existT Kundefindedinstruction ж1
                              | ipe_violation ж1         => existT Kipe_violation ж1
                              | power_up_clear            => existT Kpower_up_clear tt
                              | test_fail ж1             => existT Ktest_fail ж1
                              end
    | Uwordbyte  => fun Kv => match Kv with
                              | Byte ж1 => existT Kbyte ж1
                              | Word ж1 => existT Kword ж1
                              end
    | Uast       => fun Kv => match Kv with
                              | DOUBLEOP ж1 ж2 ж3 ж4 ж5 ж6 => existT Kdoubleop (tt, ж1, ж2, ж3, ж4, ж5, ж6)
                              | SINGLEOP ж1 ж2 ж3 ж4         => existT Ksingleop (tt, ж1, ж2, ж3, ж4)
                              | JUMP ж1 ж2                     => existT Kjump (ж1, ж2)
                              | DOESNOTUNDERSTAND ж1            => existT Kdoesnotunderstand ж1
                              end
    end.
  
  Definition record_field_type (R : recordi) : NCtx string Ty :=
    match R with
    end.
  
  Definition record_fold (R : recordi) : NamedEnv Val (record_field_type R) -> recordt R :=
    match R with
    end%exp.
  
  Definition record_unfold (R : recordi) : recordt R -> NamedEnv Val (record_field_type R) :=
    match R with
    end%env.
  
  #[export,refine] Instance typedefkit : TypeDefKit typedenotekit :=
    {| unionk           := union_constructor;
       unionk_ty        := union_constructor_type;
       recordf          := string;
       recordf_ty       := record_field_type;
       unionv_fold      := union_fold;
       unionv_unfold    := union_unfold;
       recordv_fold     := record_fold;
       recordv_unfold   := record_unfold;
    |}.
  Proof.
    - abstract (now intros [] []).
    - abstract (intros [] [[] x]; cbn in x;
                repeat
                  match goal with
                  | x: unit     |- _ => destruct x
                  | x: prod _ _ |- _ => destruct x
                  end; auto).
    - abstract (now intros [] []).
    - abstract (intros []; now apply env.Forall_forall).
  Defined.
  
  Canonical typedeclkit.
  Canonical typedenotekit.
  Canonical typedefkit.
  
  #[export] Instance varkit : VarKit := DefaultVarKit.
  
  Section RegDeclKit.
    Inductive Reg : Ty -> Set :=
      | verbosity            : Reg (ty.bvec (64))
      | old_PC_reg           : Reg (ty.wordBits)
      | PC_reg               : Reg (ty.wordBits)
      | SP_reg               : Reg (ty.wordBits)
      | SRCG1_reg            : Reg (ty.wordBits)
      | CG2_reg              : Reg (ty.wordBits)
      | R4_reg               : Reg (ty.wordBits)
      | R5_reg               : Reg (ty.wordBits)
      | R6_reg               : Reg (ty.wordBits)
      | R7_reg               : Reg (ty.wordBits)
      | R8_reg               : Reg (ty.wordBits)
      | R9_reg               : Reg (ty.wordBits)
      | R10_reg              : Reg (ty.wordBits)
      | R11_reg              : Reg (ty.wordBits)
      | R12_reg              : Reg (ty.wordBits)
      | R13_reg              : Reg (ty.wordBits)
      | R14_reg              : Reg (ty.wordBits)
      | R15_reg              : Reg (ty.wordBits)
      | MPUCTL0_reg          : Reg (ty.wordBits)
      | MPUCTL1_reg          : Reg (ty.wordBits)
      | MPUSEGB2_reg         : Reg (ty.wordBits)
      | MPUSEGB1_reg         : Reg (ty.wordBits)
      | MPUSAM_reg           : Reg (ty.wordBits)
      | MPUIPC0_reg          : Reg (ty.wordBits)
      | MPUIPSEGB2_reg       : Reg (ty.wordBits)
      | MPUIPSEGB1_reg       : Reg (ty.wordBits)
      | LastInstructionFetch : Reg (ty.union Uwordbyte).
    
    Section TransparentObligations.
      Local Set Transparent Obligations.
      Derive Signature NoConfusion NoConfusionHom EqDec for Reg.
    End TransparentObligations.
    
    Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.
    
    #[export,refine] Instance 𝑹𝑬𝑮_eq_dec : EqDec (sigT Reg) :=
      fun '(existT σ жx) '(existT τ жy) =>
      match жx, жy with
      | verbosity           , verbosity            => left eq_refl
      | old_PC_reg          , old_PC_reg           => left eq_refl
      | PC_reg              , PC_reg               => left eq_refl
      | SP_reg              , SP_reg               => left eq_refl
      | SRCG1_reg           , SRCG1_reg            => left eq_refl
      | CG2_reg             , CG2_reg              => left eq_refl
      | R4_reg              , R4_reg               => left eq_refl
      | R5_reg              , R5_reg               => left eq_refl
      | R6_reg              , R6_reg               => left eq_refl
      | R7_reg              , R7_reg               => left eq_refl
      | R8_reg              , R8_reg               => left eq_refl
      | R9_reg              , R9_reg               => left eq_refl
      | R10_reg             , R10_reg              => left eq_refl
      | R11_reg             , R11_reg              => left eq_refl
      | R12_reg             , R12_reg              => left eq_refl
      | R13_reg             , R13_reg              => left eq_refl
      | R14_reg             , R14_reg              => left eq_refl
      | R15_reg             , R15_reg              => left eq_refl
      | MPUCTL0_reg         , MPUCTL0_reg          => left eq_refl
      | MPUCTL1_reg         , MPUCTL1_reg          => left eq_refl
      | MPUSEGB2_reg        , MPUSEGB2_reg         => left eq_refl
      | MPUSEGB1_reg        , MPUSEGB1_reg         => left eq_refl
      | MPUSAM_reg          , MPUSAM_reg           => left eq_refl
      | MPUIPC0_reg         , MPUIPC0_reg          => left eq_refl
      | MPUIPSEGB2_reg      , MPUIPSEGB2_reg       => left eq_refl
      | MPUIPSEGB1_reg      , MPUIPSEGB1_reg       => left eq_refl
      | LastInstructionFetch, LastInstructionFetch => left eq_refl
      | _                   , _                    => right _
      end.
    Proof. all: transparent_abstract (intros H; depelim H). Defined.
    
    Local Obligation Tactic :=
      finite_from_eqdec.
    
    Program Instance 𝑹𝑬𝑮_finite : Finite (sigT Reg) :=
      {|
        enum := [
                  existT _ verbosity;
                  existT _ old_PC_reg;
                  existT _ PC_reg;
                  existT _ SP_reg;
                  existT _ SRCG1_reg;
                  existT _ CG2_reg;
                  existT _ R4_reg;
                  existT _ R5_reg;
                  existT _ R6_reg;
                  existT _ R7_reg;
                  existT _ R8_reg;
                  existT _ R9_reg;
                  existT _ R10_reg;
                  existT _ R11_reg;
                  existT _ R12_reg;
                  existT _ R13_reg;
                  existT _ R14_reg;
                  existT _ R15_reg;
                  existT _ MPUCTL0_reg;
                  existT _ MPUCTL1_reg;
                  existT _ MPUSEGB2_reg;
                  existT _ MPUSEGB1_reg;
                  existT _ MPUSAM_reg;
                  existT _ MPUIPC0_reg;
                  existT _ MPUIPSEGB2_reg;
                  existT _ MPUIPSEGB1_reg;
                  existT _ LastInstructionFetch
                ]
      |}.
  End RegDeclKit.
  
  Section MemoryModel.
    (*TODO*)
    Definition Memory :=
      Z -> Z.
  End MemoryModel.
  
  Include BaseMixin.
End UntitledBase.



Theorem UNTRANSLATED_DEFINITIONS : False. Qed.

(*

----
  val __deref = monadic {_: "reg_deref"}: forall ('a : Type). register('a) -> 'a

OCaml location: nanosail/SailToNanosail/Translate/Recursive.ml line 68
Sail location: File "/home/ale/documenti/uni/magistrale/tesi/_opam/share/sail/lib/flow.sail" line 131 chars 55-63
Message: unknown type register
----

----
  $[complete]
  function encdec_backwards arg# = let head_exp# = arg# in
    $[complete] $[mapping_match] match let v__5 = head_exp# in
      if let mapping0# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__5, 15, 12) in
      let mapping5# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__5, 3, 0) in
      let mapping4# : bitvector(2) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__5, 5, 4) in
      let mapping3# : bitvector(1) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__5, 6, 6) in
      let mapping2# : bitvector(1) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__5, 7, 7) in
      let mapping1# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__5, 11, 8) in
      let mapping0# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__5, 15, 12) in
        and_bool(encdec_doubleop_backwards_matches(mapping0#), and_bool(RegisterMapping_backwards_matches(mapping1#), and_bool(destinationmaping_backwards_matches(mapping2#), and_bool(bitmaping_backwards_matches(mapping3#), and_bool(sourcemaping_backwards_matches(mapping4#), RegisterMapping_backwards_matches(mapping5#)))))) then
        let mapping0# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__5, 15, 12) in
        let mapping5# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__5, 3, 0) in
        let mapping4# : bitvector(2) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__5, 5, 4) in
        let mapping3# : bitvector(1) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__5, 6, 6) in
        let mapping2# : bitvector(1) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__5, 7, 7) in
        let mapping1# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__5, 11, 8) in
        let mapping0# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__5, 15, 12) in
          $[complete] match (encdec_doubleop_backwards(mapping0#), RegisterMapping_backwards(mapping1#), destinationmaping_backwards(mapping2#), bitmaping_backwards(mapping3#), sourcemaping_backwards(mapping4#), RegisterMapping_backwards(mapping5#)) {
            (op, sourceReg, Ad, bw, As, destinationReg) => Some(DOUBLEOP((op, bw, sourceReg, As, destinationReg, Ad)))
          }
      else
        None() {
      Some(result) => result,
      None(_) => let head_exp# = head_exp# in
        $[complete] $[mapping_match] match let v__4 = head_exp# in
          if let mapping6# : bitvector(9) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__4, 15, 7) in
          let mapping9# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__4, 3, 0) in
          let mapping8# : bitvector(2) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__4, 5, 4) in
          let mapping7# : bitvector(1) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__4, 6, 6) in
          let mapping6# : bitvector(9) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__4, 15, 7) in
            and_bool(encdec_singleop_backwards_matches(mapping6#), and_bool(bitmaping_backwards_matches(mapping7#), and_bool(sourcemaping_backwards_matches(mapping8#), RegisterMapping_backwards_matches(mapping9#)))) then
            let mapping6# : bitvector(9) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__4, 15, 7) in
            let mapping9# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__4, 3, 0) in
            let mapping8# : bitvector(2) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__4, 5, 4) in
            let mapping7# : bitvector(1) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__4, 6, 6) in
            let mapping6# : bitvector(9) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__4, 15, 7) in
              $[complete] match (encdec_singleop_backwards(mapping6#), bitmaping_backwards(mapping7#), sourcemaping_backwards(mapping8#), RegisterMapping_backwards(mapping9#)) {
                (op, bw, As, reg) => Some(SINGLEOP((op, bw, As, reg)))
              }
          else
            None() {
          Some(result) => result,
          None(_) => let head_exp# = head_exp# in
            $[complete] $[mapping_match] match let v__2 = head_exp# in
              if and_bool(let mapping10# : bitvector(3) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__2, 12, 10) in
                encdec_jump_backwards_matches(mapping10#), $[overloaded { "name" = "==", "is_infix" = true }] eq_bits($[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__2, 15, 13), [bitzero, bitzero, bitone])) then
                let offset : Offset = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__2, 9, 0) in
                let mapping10# : bitvector(3) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__2, 12, 10) in
                  $[complete] match encdec_jump_backwards(mapping10#) {op => Some(JUMP((op, offset)))}
              else
                None() {
              Some(result) => result,
              None(_) => $[incomplete] match head_exp# {a : bits(16) => DOESNOTUNDERSTAND(a)}
            }
        }
    }

OCaml location: nanosail/SailToNanosail/Translate/Recursive.ml line 68
Sail location: UnknownLocation
Message: unknown type option
----

----
  $[complete]
  function encdec_backwards_matches arg# = let head_exp# = arg# in
    $[complete] $[mapping_match] match let v__9 = head_exp# in
      if let mapping0# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__9, 15, 12) in
      let mapping5# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__9, 3, 0) in
      let mapping4# : bitvector(2) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__9, 5, 4) in
      let mapping3# : bitvector(1) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__9, 6, 6) in
      let mapping2# : bitvector(1) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__9, 7, 7) in
      let mapping1# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__9, 11, 8) in
      let mapping0# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__9, 15, 12) in
        and_bool(encdec_doubleop_backwards_matches(mapping0#), and_bool(RegisterMapping_backwards_matches(mapping1#), and_bool(destinationmaping_backwards_matches(mapping2#), and_bool(bitmaping_backwards_matches(mapping3#), and_bool(sourcemaping_backwards_matches(mapping4#), RegisterMapping_backwards_matches(mapping5#)))))) then
        let mapping0# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__9, 15, 12) in
        let mapping5# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__9, 3, 0) in
        let mapping4# : bitvector(2) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__9, 5, 4) in
        let mapping3# : bitvector(1) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__9, 6, 6) in
        let mapping2# : bitvector(1) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__9, 7, 7) in
        let mapping1# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__9, 11, 8) in
        let mapping0# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__9, 15, 12) in
          $[complete] match (encdec_doubleop_backwards(mapping0#), RegisterMapping_backwards(mapping1#), destinationmaping_backwards(mapping2#), bitmaping_backwards(mapping3#), sourcemaping_backwards(mapping4#), RegisterMapping_backwards(mapping5#)) {
            (op, sourceReg, Ad, bw, As, destinationReg) => Some(true)
          }
      else
        None() {
      Some(result) => result,
      None(_) => let head_exp# = head_exp# in
        $[complete] $[mapping_match] match let v__8 = head_exp# in
          if let mapping6# : bitvector(9) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__8, 15, 7) in
          let mapping9# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__8, 3, 0) in
          let mapping8# : bitvector(2) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__8, 5, 4) in
          let mapping7# : bitvector(1) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__8, 6, 6) in
          let mapping6# : bitvector(9) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__8, 15, 7) in
            and_bool(encdec_singleop_backwards_matches(mapping6#), and_bool(bitmaping_backwards_matches(mapping7#), and_bool(sourcemaping_backwards_matches(mapping8#), RegisterMapping_backwards_matches(mapping9#)))) then
            let mapping6# : bitvector(9) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__8, 15, 7) in
            let mapping9# : bitvector(4) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__8, 3, 0) in
            let mapping8# : bitvector(2) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__8, 5, 4) in
            let mapping7# : bitvector(1) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__8, 6, 6) in
            let mapping6# : bitvector(9) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__8, 15, 7) in
              $[complete] match (encdec_singleop_backwards(mapping6#), bitmaping_backwards(mapping7#), sourcemaping_backwards(mapping8#), RegisterMapping_backwards(mapping9#)) {
                (op, bw, As, reg) => Some(true)
              }
          else
            None() {
          Some(result) => result,
          None(_) => let head_exp# = head_exp# in
            $[complete] $[mapping_match] match let v__6 = head_exp# in
              if and_bool(let mapping10# : bitvector(3) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__6, 12, 10) in
                encdec_jump_backwards_matches(mapping10#), $[overloaded { "name" = "==", "is_infix" = true }] eq_bits($[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__6, 15, 13), [bitzero, bitzero, bitone])) then
                let mapping10# : bitvector(3) = $[overloaded { "name" = "vector_subrange", "is_infix" = false }] subrange_bits(v__6, 12, 10) in
                  $[complete] match encdec_jump_backwards(mapping10#) {op => Some(true)}
              else
                None() {
              Some(result) => result,
              None(_) => $[incomplete] match head_exp# {a : bits(16) => true}
            }
        }
    }

OCaml location: nanosail/SailToNanosail/Translate/Recursive.ml line 68
Sail location: UnknownLocation
Message: unknown type option
----

*)
