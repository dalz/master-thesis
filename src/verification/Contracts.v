From Coq Require Import
  Lists.List
  Strings.String
  ZArith
  Lia.

From Katamaran Require Import
     Notations
     Specification
     Assertions
     Bitvector
     MicroSail.SymbolicExecutor
     MicroSail.Soundness.

Require Import
  Machine
  Sig.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import bv.notations.
Import ListNotations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Import asn.notations.

Import MSP430Program.

Definition I := Logic.I.

Module Import MSP430Specification <: Specification MSP430Base MSP430Signature MSP430Program.
  Include SpecificationMixin MSP430Base MSP430Signature MSP430Program.

  Definition SepContractFun {Δ τ} (f : Fun Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepContractFunX {Δ τ} (f : FunX Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepLemma {Δ} (f : Lem Δ) : Type :=
    Lemma Δ.

  Section ContractDefKit.
    Local Notation "r m↦ v" := (asn.chunk (chunk_user ptstomem [r; v])) (at level 70).
    Local Notation "x <> y" := (asn.formula (formula_relop bop.neq x y)) : asn_scope.
    (* Local Notation "x <> y" := (term_binop (bop.relop bop.neq) x y) : asn_scope. *)

    (* Definition match_bw {Σ} x b w : Assertion Σ := *)
    (*   (asn.match_enum Ebw x *)
    (*      (fun bw => match bw with *)
    (*                 | BYTE_INSTRUCTION => b *)
    (*                 | WORD_INSTRUCTION => w *)
    (*                 end)). *)

    (* need to be angelic otherwise read_mem_aux contract gives an error - why? *)
    Local Notation asn_accessible_addresses segb1 segb2 :=
      (asn.chunk_angelic (chunk_user accessible_addresses
                            [term_var segb1; term_var segb2])).

    Local Notation asn_accessible_addresses_without segb1 segb2 addr :=
      (asn.chunk_angelic (chunk_user accessible_addresses_without
                            [term_var segb1; term_var segb2; term_var addr])).

    (* Predicates *)

    Definition word_times_16 {Σ} (w : Term Σ ty.wordBits) : Term Σ ty.int :=
      (term_binop bop.times
         (term_unsigned w)
         (term_val ty.int 16)).

    Definition term_plus {Σ} (m : Z) (n : Term Σ ty.int) : Term Σ ty.int :=
      (term_binop bop.plus n (term_val ty.int m)).

    Definition term_word_plus {Σ} (m : bv 16) (n : Term Σ ty.wordBits) : Term Σ ty.wordBits :=
      term_binop bop.bvadd n (term_val ty.wordBits m).

    Definition asn_ipe_entry_point {Σ}
      (segb1 addr : Term Σ ty.wordBits)
      : Assertion Σ
    :=
      asn.formula
        (formula_relop bop.eq
           (term_plus 8 (word_times_16 segb1))
           (term_unsigned addr)).

    (* True when executing code at PC does not grant access to the IPE region.

       The precise definition would be:
       - PC outside the IPE region, or
       - PC within first 8 bytes of the IPE region.

       Additionally, if the IVT and RV are in the IPE region, they are always
       accessible for reading and writing, and execution from them is
       prohibited (see section 9.4.1 of slau367p).

       However:
       - we don't support the IVT and RV, so don't care about that special case;
       - treat the first 8 bytes as trusted.

       The latter means that our contracts don't guarantee anything about code
       executed from the first 8 bytes of the IPE region (since they all assume
       asn_untrusted), but also they guarantee that untrusted code cannot jump
       to there in the first place.
    *)
    Definition asn_untrusted {Σ}
      (segb1 segb2 pc : Term Σ ty.wordBits)
      : Assertion Σ
    :=
      asn.formula (formula_user untrusted [segb1;segb2;pc]).

    Definition asn_untrusted_or_entry_point {Σ}
      (segb1 segb2 pc : Term Σ ty.wordBits) : Assertion Σ
      := asn_ipe_entry_point segb1 pc ∨ asn_untrusted segb1 segb2 pc.

    Definition asn_ipe_configured {Σ} (ipectl segb1 segb2 : Term Σ ty.wordBits) :=
      asn.formula
        (formula_and
          (formula_and
             (* enabled *)
             (formula_relop bop.eq
                (term_vector_subrange 6 1 ipectl)
                (term_val (ty.bvec 1) [bv 0x1]))
             (* locked *)
             (formula_relop bop.eq
                (term_vector_subrange 7 1 ipectl)
                (term_val (ty.bvec 1) [bv 0x1])))
          (* segb1 < segb2 *)
          (formula_relop bop.lt
             (term_unsigned segb1)
             (term_unsigned segb2))).

    Definition asn_mpu_registers {Σ} : Assertion Σ :=
        ∃ "MPUCTL0_reg"    , MPUCTL0_reg    ↦ term_var "MPUCTL0_reg"
      ∗ ∃ "MPUCTL1_reg"    , MPUCTL1_reg    ↦ term_var "MPUCTL1_reg"
      ∗ ∃ "MPUSEGB2_reg"   , MPUSEGB2_reg   ↦ term_var "MPUSEGB2_reg"
      ∗ ∃ "MPUSEGB1_reg"   , MPUSEGB1_reg   ↦ term_var "MPUSEGB1_reg"
      ∗ ∃ "MPUSAM_reg"     , MPUSAM_reg     ↦ term_var "MPUSAM_reg".

    (*
    Definition asn_own_sample_regs {Σ} : Assertion Σ :=
        ∃ "SP"    , SP_reg               ↦ term_var "SP"
      ∗ ∃ "SRCG1" , SRCG1_reg            ↦ term_var "SRCG1"
      ∗ ∃ "CG2"   , CG2_reg              ↦ term_var "CG2"
      ∗ ∃ "R4"    , R4_reg               ↦ term_var "R4"
      ∗ ∃ "R5"    , R5_reg               ↦ term_var "R5"
      ∗ ∃ "R6"    , R6_reg               ↦ term_var "R6"
      ∗ ∃ "R7"    , R7_reg               ↦ term_var "R7"
      ∗ ∃ "R8"    , R8_reg               ↦ term_var "R8"
      ∗ ∃ "R9"    , R9_reg               ↦ term_var "R9"
      ∗ ∃ "R10"   , R10_reg              ↦ term_var "R10"
      ∗ ∃ "R11"   , R11_reg              ↦ term_var "R11"
      ∗ ∃ "R12"   , R12_reg              ↦ term_var "R12"
      ∗ ∃ "R13"   , R13_reg              ↦ term_var "R13"
      ∗ ∃ "R14"   , R14_reg              ↦ term_var "R14"
      ∗ ∃ "R15"   , R15_reg              ↦ term_var "R15"
      ∗ ∃ "LIF"   , LastInstructionFetch ↦ term_var "LIF".
    *)

    Definition asn_own_sample_regs {Σ} : Assertion Σ :=
      (* actual sample registers (except PC) *)
        ∃ "SRCG1" , SRCG1_reg            ↦ term_var "SRCG1"
      ∗ ∃ "R4"    , R4_reg               ↦ term_var "R4"

      (* often needed *)
      ∗ ∃ "SP"    , SP_reg               ↦ term_var "SP"
      ∗ ∃ "LIF"   , LastInstructionFetch ↦ term_var "LIF".

    Definition asn_is_sample_reg {Σ} (reg : Term Σ (ty.enum Eregister)) : Assertion Σ :=
        reg = term_val (ty.enum Eregister) PC
      ∨ reg = term_val (ty.enum Eregister) SRCG1
      ∨ reg = term_val (ty.enum Eregister) R4.

    (* Lemmas *)

    Definition lemma_extract_accessible_ptsto : SepLemma extract_accessible_ptsto :=
      {|
        lemma_logic_variables :=
          ["addr" :: ty.Address; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits];

        lemma_patterns := [term_var "addr"];

        lemma_precondition :=
            MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "addr");

        lemma_postcondition :=
            MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses_without "segb1" "segb2" "addr"
          ∗ ∃ "v", term_var "addr" m↦ term_var "v";
      |}.

    Definition lemma_return_accessible_ptsto : SepLemma return_accessible_ptsto :=
      {|
        lemma_logic_variables :=
          [ "addr" :: ty.Address; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits ];

        lemma_patterns := [term_var "addr"];

        lemma_precondition :=
            asn_accessible_addresses_without "segb1" "segb2" "addr"
          ∗ ∃ "v", term_var "addr" m↦ term_var "v";

        lemma_postcondition := asn_accessible_addresses "segb1" "segb2";
      |}.

    Definition lemma_open_ptsto_instr : SepLemma open_ptsto_instr :=
      {|
        lemma_logic_variables := ["addr" :: ty.Address];
        lemma_patterns        := [term_var "addr"];
        lemma_precondition    := ⊤;
        lemma_postcondition   := ⊤;
      |}.

    Definition lemma_close_ptsto_instr : SepLemma close_ptsto_instr :=
      {|
        lemma_logic_variables := ["addr" :: ty.Address; "w" :: ty.wordBits];
        lemma_patterns        := [term_var "addr"(* ; term_var "w" *)];
        lemma_precondition    := ⊤;
        lemma_postcondition   := ⊤;
      |}.

    (* Foreign function contracts *)

    Definition sep_contract_undefined_bitvector (n : nat) :
      SepContractFunX (@undefined_bitvector n) :=
      {|
        sep_contract_logic_variables := ["_" :: ty.int];
        sep_contract_localstore      := [term_var "_"];
        sep_contract_precondition    := ⊤;
        sep_contract_result          := "v";
        sep_contract_postcondition   := ⊤;
      |}.

    Definition sep_contract_read_ram :
      SepContractFunX read_ram :=
      {|
        sep_contract_logic_variables := ["addr" :: ty.Address; "v" :: ty.byteBits];
        sep_contract_localstore      := [term_var "addr"];
        sep_contract_precondition    := term_var "addr" m↦ term_var "v";
        sep_contract_result          := "w";
        sep_contract_postcondition   :=
          term_var "v" = term_var "w" ∗ term_var "addr" m↦ term_var "v";
      |}.

    Definition sep_contract_write_ram :
      SepContractFunX write_ram :=
      {|
        sep_contract_logic_variables :=
          ["addr" :: ty.Address; "v" :: ty.byteBits; "w" :: ty.byteBits];

        sep_contract_localstore      := [term_var "addr"; term_var "v"];
        sep_contract_precondition    := term_var "addr" m↦ term_var "w";
        sep_contract_result          := "u";
        sep_contract_postcondition   :=
          term_var "addr" m↦ term_var "v"
          ∗ term_var "u" = term_val ty.unit tt;
      |}.

    Definition sep_contract_decode : SepContractFunX decode :=
      {|
        sep_contract_logic_variables := ["w" :: ty.union Uwordbyte];
        sep_contract_localstore      := [term_var "w"];
        sep_contract_precondition    := ⊤;
        sep_contract_result          := "i";
        sep_contract_postcondition   := ⊤;
      |}.

    (* μSail function contracts *)

    Definition sep_contract_check_byte_access :
      SepContractFun check_byte_access :=
      {|
        sep_contract_logic_variables :=
          [ "addr"   :: ty.Address
          ; "jump"   :: ty.bool
          ; "ipectl" :: ty.wordBits
          ; "segb1"  :: ty.wordBits
          ; "segb2"  :: ty.wordBits
          ; "pc"     :: ty.wordBits
          ];

        sep_contract_localstore := [term_var "addr"; term_var "jump"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
          ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "pc");

        sep_contract_result        := "v";
        sep_contract_postcondition :=
            term_var "v" = term_val ty.unit tt

          ∗ PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ (asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "addr")
             ∨ (asn.formula (formula_bool (term_var "jump"))
                ∗ asn_ipe_entry_point (term_var "segb1") (term_var "addr")))
      |}.

    Definition sep_contract_read_mem_aux :
      SepContractFun read_mem_aux :=
      {|
        sep_contract_logic_variables :=
          [ "bw" :: ty.enum Ebw; "addr" :: ty.Address
          ; "ipectl" :: ty.wordBits; "segb1"  :: ty.wordBits; "segb2"  :: ty.wordBits
          ; "pc" :: ty.wordBits
          ];

        sep_contract_localstore := [term_var "bw"; term_var "addr"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
          ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "pc")

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_mpu_registers;

        sep_contract_result        := "v";
        sep_contract_postcondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_mpu_registers;
      |}.

    Definition sep_contract_write_mpu_reg_byte :
      SepContractFun write_mpu_reg_byte :=
      {|
        sep_contract_logic_variables :=
          [ "addr" :: ty.Address; "v" :: ty.byteBits
          ; "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits];

        sep_contract_localstore := [term_var "addr"; term_var "v"];

        sep_contract_precondition :=
            MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
          ∗ asn_mpu_registers;

        sep_contract_result := "u";
        sep_contract_postcondition :=
            term_var "u" = term_val ty.unit tt

          ∗ MPUIPC0_reg ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_mpu_registers;
      |}.

    Definition sep_contract_writeMem :
      SepContractFun writeMem :=
      {|
        sep_contract_logic_variables :=
          [ "bw" :: ty.enum Ebw; "addr" :: ty.Address; "v" :: ty.union Uwordbyte
          ; "ipectl" :: ty.wordBits; "segb1"  :: ty.wordBits; "segb2"  :: ty.wordBits
          ; "pc" :: ty.wordBits
          ];

        sep_contract_localstore := [term_var "bw"; term_var "addr"; term_var "v"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
          ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "pc")

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_mpu_registers;

        sep_contract_result        := "v";
        sep_contract_postcondition :=
            term_var "v" = term_val ty.unit tt

          ∗ PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_mpu_registers;
      |}.

    Definition sep_contract_setPC :
      SepContractFun setPC :=
      {|
        sep_contract_logic_variables :=
          [ "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc_old" :: ty.wordBits; "pc_new" :: ty.wordBits ];

        sep_contract_localstore := [term_var "pc_new"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc_old"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
          ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "pc_old");

        sep_contract_result          := "u";
        sep_contract_postcondition   :=
            term_var "u" = term_val ty.unit tt

          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ PC_reg ↦ term_var "pc_new"
          ∗ asn_untrusted_or_entry_point
              (term_var "segb1") (term_var "segb2") (term_var "pc_new");
      |}.

    Definition sep_contract_incPC :
      SepContractFun incPC :=
      {|
        sep_contract_logic_variables :=
          [ "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc_old" :: ty.wordBits
          ; "u" :: ty.unit ];

        sep_contract_localstore := [ term_var "u" ];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc_old"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
          ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "pc_old");

        sep_contract_result          := "v";
        sep_contract_postcondition   :=
            term_var "v" = term_val ty.unit tt

          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ ∃ "pc_new",
            ( term_var "pc_new" = term_word_plus [bv 2] (term_var "pc_old")
            ∗ PC_reg ↦ term_var "pc_new"
            ∗ asn_untrusted
                (term_var "segb1") (term_var "segb2") (term_var "pc_new"));
      |}.

    Definition sep_contract_fetch :
    SepContractFun fetch :=
    {|
      sep_contract_logic_variables :=
        [ "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
        ; "pc_old" :: ty.wordBits
        ; "u" :: ty.unit ];

      sep_contract_localstore := [ term_var "u" ];

      sep_contract_precondition :=
          PC_reg         ↦ term_var "pc_old"
        ∗ MPUIPC0_reg    ↦ term_var "ipectl"
        ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
        ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

        ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
        ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "pc_old")

        ∗ asn_accessible_addresses "segb1" "segb2"
        ∗ asn_mpu_registers;

      sep_contract_result          := "v";
      sep_contract_postcondition   :=
          MPUIPC0_reg    ↦ term_var "ipectl"
        ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
        ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

        ∗ asn_accessible_addresses "segb1" "segb2"
        ∗ asn_mpu_registers

        ∗ ∃ "pc_new",
          ( (* term_var "pc_new" = term_word_plus [bv 2] (term_var "pc_old") *)
            (* ∗ *) PC_reg ↦ term_var "pc_new"
            ∗ asn_untrusted
                (term_var "segb1") (term_var "segb2") (term_var "pc_new"));
    |}.

    Definition sep_contract_read_register : SepContractFun read_am_register :=
      {|
        sep_contract_logic_variables :=
          [ "bw" :: ty.enum Ebw; "reg" :: ty.enum Eregister; "pc" :: ty.wordBits];

        sep_contract_localstore := [term_var "bw"; term_var "reg"];

        sep_contract_precondition :=
            PC_reg ↦ term_var "pc"
          ∗ asn_own_sample_regs
          ∗ asn_is_sample_reg (term_var "reg");

        sep_contract_result          := "v";
        sep_contract_postcondition   :=
            (  ∃ "b", (term_var "v" = term_union Uwordbyte Kbyte (term_var "b"))
             ∨ ∃ "w", (term_var "v" = term_union Uwordbyte Kword (term_var "w")
                       ∗ (term_var "w" = term_var "pc"
                          ∨ (term_var "reg" <> term_enum Eregister PC))))

          ∗ PC_reg ↦ term_var "pc"
          ∗ asn_own_sample_regs;
      |}.

    Definition sep_contract_write_register : SepContractFun write_am_register :=
      {|
        sep_contract_logic_variables :=
          [ "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc_old" :: ty.wordBits
          ; "bw" :: ty.enum Ebw; "reg" :: ty.enum Eregister; "v" :: ty.union Uwordbyte
          ];

        sep_contract_localstore := [term_var "bw"; term_var "reg"; term_var "v"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc_old"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
          ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "pc_old")
          ∗ asn_is_sample_reg (term_var "reg")

          ∗ asn_own_sample_regs;

        sep_contract_result          := "u";
        sep_contract_postcondition   :=
            term_var "u" = term_val ty.unit tt

          ∗ (PC_reg ↦ term_var "pc_old"
             ∨ (term_var "reg" = term_val (ty.enum Eregister) PC
                ∗ ∃ "pc_new",
                  (PC_reg ↦ term_var "pc_new"
                   ∗ asn_untrusted_or_entry_point
                       (term_var "segb1") (term_var "segb2") (term_var "pc_new")

                   (* special case for the write in read_autoincrement,
                      we want to know the value of pc_new *)
                   ∗ (term_var "bw" = term_enum Ebw WORD_INSTRUCTION
                      ∗ (term_var "v" = term_union Uwordbyte Kword (term_var "pc_new")
                         ∨ ∃ "b", term_var "v" = term_union Uwordbyte Kbyte (term_var "b"))

                      (* don't care *)
                      ∨ term_var "bw" = term_enum Ebw BYTE_INSTRUCTION))))

          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_own_sample_regs;
      |}.

    Definition sep_contract_read_indexed : SepContractFun read_indexed :=
      {|
        sep_contract_logic_variables :=
          [ "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc_old" :: ty.wordBits
          ; "bw" :: ty.enum Ebw; "reg" :: ty.enum Eregister
          ];

        sep_contract_localstore := [term_var "bw"; term_var "reg"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc_old"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
          ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "pc_old")
          ∗ asn_is_sample_reg (term_var "reg")

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_mpu_registers
          ∗ asn_own_sample_regs;

        sep_contract_result          := "v";
        sep_contract_postcondition   :=
            (* pc_old + 2 except when reading from CG2 *)
            ∃ "pc_new",
              ( PC_reg ↦ term_var "pc_new"
              ∗ asn_untrusted
                  (term_var "segb1") (term_var "segb2") (term_var "pc_new"))

          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_mpu_registers
          ∗ asn_own_sample_regs;
      |}.

    Definition sep_contract_read_indirect : SepContractFun read_indirect :=
      {|
        sep_contract_logic_variables :=
          [ "pc" :: ty.wordBits; "ipectl" :: ty.wordBits
          ; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "bw" :: ty.enum Ebw; "reg" :: ty.enum Eregister
          ];

        sep_contract_localstore := [term_var "bw"; term_var "reg"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
          ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "pc")
          ∗ asn_is_sample_reg (term_var "reg")

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_mpu_registers
          ∗ asn_own_sample_regs;

        sep_contract_result          := "v";
        sep_contract_postcondition   :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses  "segb1" "segb2"
          ∗ asn_mpu_registers
          ∗ asn_own_sample_regs;
      |}.

    Definition sep_contract_read_autoincrement : SepContractFun read_autoincrement :=
      {|
        sep_contract_logic_variables :=
          [ "pc_old" :: ty.wordBits
          ; "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "bw" :: ty.enum Ebw; "reg" :: ty.enum Eregister
          ];

        sep_contract_localstore := [term_var "bw"; term_var "reg"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc_old"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
          ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "pc_old")
          ∗ asn_is_sample_reg (term_var "reg")

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_mpu_registers
          ∗ asn_own_sample_regs;

        sep_contract_result          := "v";
        sep_contract_postcondition   :=
            ∃ "pc_new",
              (PC_reg ↦ term_var "pc_new"
               ∗ asn_untrusted
                   (term_var "segb1") (term_var "segb2") (term_var "pc_new"))

          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses  "segb1" "segb2"
          ∗ asn_mpu_registers
          ∗ asn_own_sample_regs;
      |}.

    Definition sep_contract_write_indexed : SepContractFun write_indexed :=
      {|
        sep_contract_logic_variables :=
          [ "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc" :: ty.wordBits
          ; "bw" :: ty.enum Ebw; "reg" :: ty.enum Eregister; "v" :: ty.union Uwordbyte
          ];

        sep_contract_localstore := [term_var "bw"; term_var "reg"; term_var "v"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
          ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "pc")
          ∗ asn_is_sample_reg (term_var "reg")

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_mpu_registers
          ∗ asn_own_sample_regs;

        sep_contract_result          := "u";
        sep_contract_postcondition   :=
            term_var "u" = term_val ty.unit tt

            (* PC is changed in move_inst, unlike read_indexed *)
          ∗ PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_mpu_registers
          ∗ asn_own_sample_regs;
      |}.

    Definition sep_contract_execute_move : SepContractFun execute :=
      {|
        sep_contract_logic_variables :=
          [ "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc_old" :: ty.wordBits
          ; "instr" :: ty.union Uast; "bw" :: ty.enum Ebw
          ; "src_reg" :: ty.enum Eregister; "dest_reg" :: ty.enum Eregister
          ; "src_am" :: ty.enum Eam; "dest_am" :: ty.enum Eam
          ];

        sep_contract_localstore := [term_var "instr"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc_old"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
          ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "pc_old")
          ∗ asn_is_sample_reg (term_var "src_reg")
          ∗ asn_is_sample_reg (term_var "dest_reg")

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_mpu_registers
          ∗ asn_own_sample_regs

          ∗ term_var "instr" =
              term_union Uast Kdoubleop
                (term_tuple
                   [term_val (ty.enum Edoubleop) MOV;
                    term_var "bw";
                    term_var "src_reg";
                    term_var "src_am";
                    term_var "dest_reg";
                    term_var "dest_am"]);

        sep_contract_result          := "u";
        sep_contract_postcondition   :=
            term_var "u" = term_val ty.unit tt

          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ ∃ "pc_new",
            (PC_reg ↦ term_var "pc_new"
               ∗ asn_untrusted_or_entry_point (term_var "segb1") (term_var "segb2") (term_var "pc_new"))

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_mpu_registers
          ∗ asn_own_sample_regs;
      |}.

    Definition sep_contract_execute_jump :
      SepContractFun execute :=
      {|
        sep_contract_logic_variables :=
          [ "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc" :: ty.wordBits; "srcg1" :: ty.wordBits
          ; "instr" :: ty.union Uast; "jump_arg" :: unionk_ty Uast Kjump ];

        sep_contract_localstore := [term_var "instr"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc"
          ∗ SRCG1_reg      ↦ term_var "srcg1"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
          ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "pc")

          ∗ term_var "instr" = term_union Uast Kjump (term_var "jump_arg");

        sep_contract_result          := "u";
        sep_contract_postcondition   :=
            term_var "u" = term_val ty.unit tt

          ∗ SRCG1_reg      ↦ term_var "srcg1"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ ∃ "pc_new",
            ( PC_reg ↦ term_var "pc_new"
            ∗ asn_untrusted_or_entry_point
                (term_var "segb1") (term_var "segb2") (term_var "pc_new"));
      |}.

    Definition sep_contract_execute_call :
      SepContractFun execute :=
      {|
        sep_contract_logic_variables :=
          [ "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc_old" :: ty.wordBits
          ; "bw" :: ty.enum Ebw; "reg" :: ty.enum Eregister; "am" :: ty.enum Eam
          ; "instr" :: ty.union Uast ];

        sep_contract_localstore := [term_var "instr"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc_old"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_ipe_configured (term_var "ipectl") (term_var "segb1") (term_var "segb2")
          ∗ asn_untrusted (term_var "segb1") (term_var "segb2") (term_var "pc_old")
          ∗ asn_is_sample_reg (term_var "reg")

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_mpu_registers
          ∗ asn_own_sample_regs

          ∗ term_var "instr" =
              term_union Uast Ksingleop
                (term_tuple
                   [ term_val (ty.enum Esingleop) CALL
                   ; term_var "bw"
                   ; term_var "am"
                   ; term_var "reg"]);

        sep_contract_result          := "u";
        sep_contract_postcondition   :=
            term_var "u" = term_val ty.unit tt

          ∗ ∃ "pc_new",
            ( PC_reg ↦ term_var "pc_new"
            ∗ asn_untrusted_or_entry_point
                (term_var "segb1") (term_var "segb2") (term_var "pc_new"))

          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses "segb1" "segb2"
          ∗ asn_mpu_registers
          ∗ asn_own_sample_regs
      |}.

    (* The following maps μSail function names to their contracts. *)
    Definition CEnv : SepContractEnv :=
      fun Δ τ f =>
        match f with
        | check_byte_access => Some sep_contract_check_byte_access
        | read_mem_aux => Some sep_contract_read_mem_aux
        | write_mpu_reg_byte => Some sep_contract_write_mpu_reg_byte
        | writeMem => Some sep_contract_writeMem
        | setPC => Some sep_contract_setPC
        | incPC => Some sep_contract_incPC
        | fetch => Some sep_contract_fetch
        | read_am_register => Some sep_contract_read_register
        | read_indexed => Some sep_contract_read_indexed
        | read_indirect => Some sep_contract_read_indirect
        | read_autoincrement => Some sep_contract_read_autoincrement
        | write_am_register => Some sep_contract_write_register
        | write_indexed => Some sep_contract_write_indexed
        | _ => None
        end.

    (* And this definition maps foreign functions to their contracts. *)
    Definition CEnvEx : SepContractEnvEx :=
      fun Δ τ f =>
        match f with
        | @undefined_bitvector n => sep_contract_undefined_bitvector n
        | read_ram => sep_contract_read_ram
        | write_ram => sep_contract_write_ram
        | decode => sep_contract_decode
        end.

    (* And finally a mapping from ghost lemmas to the entailments they encode. *)
    Definition LEnv : LemmaEnv :=
      fun Δ l =>
        match l with
        | extract_accessible_ptsto => lemma_extract_accessible_ptsto
        | return_accessible_ptsto => lemma_return_accessible_ptsto
        | open_ptsto_instr => lemma_open_ptsto_instr
        | close_ptsto_instr => lemma_close_ptsto_instr
        end.
  End ContractDefKit.
End MSP430Specification.

(*** VERIFICATION ***)

Import MSP430Specification.
Import SymProp.notations.
Import Erasure.notations.

Module MSP430Executor :=
  MakeExecutor MSP430Base MSP430Signature MSP430Program MSP430Specification.

Import MSP430Executor.
Import MSP430Executor.Symbolic.

Ltac symbolic_simpl :=
  apply validcontract_with_erasure_and_fuel_sound;
  compute;
  constructor;
  simpl.

Lemma valid_contract_check_byte_access : Symbolic.ValidContractWithFuel 10 sep_contract_check_byte_access fun_check_byte_access.
Proof.
  symbolic_simpl.
  repeat split;
    unfold puntrusted in *;
    try lia.
  congruence.
Qed.

Lemma valid_contract_read_mem_aux : Symbolic.ValidContractWithFuel 10 sep_contract_read_mem_aux fun_read_mem_aux.
Proof. now apply validcontract_reflect_fuel_sound. Qed.

Lemma valid_contract_write_mpu_reg_byte : Symbolic.ValidContractWithFuel 10 sep_contract_write_mpu_reg_byte fun_write_mpu_reg_byte.
Proof.
  symbolic_simpl.
  repeat split; congruence.
Qed.

Lemma valid_contract_writeMem : Symbolic.ValidContractWithFuel 10 sep_contract_writeMem fun_writeMem.
Proof. now apply validcontract_reflect_fuel_sound. Qed.

Lemma valid_contract_setPC : Symbolic.ValidContractWithFuel 10 sep_contract_setPC fun_setPC.
Proof. now apply validcontract_reflect_fuel_sound. Qed.

Lemma valid_contract_incPC : Symbolic.ValidContractWithFuel 10 sep_contract_incPC fun_incPC.
Proof.
  symbolic_simpl.
  repeat split; intros; unfold puntrusted in *.
  destruct (bv.unsigned_bounds v2).
  destruct (bv.unsigned_add_view v2 [bv 0x2]); cbn in *; lia.
Qed.

Lemma valid_contract_fetch : Symbolic.ValidContractWithFuel 10 sep_contract_fetch fun_fetch.
Proof. now symbolic_simpl. Qed.

Lemma valid_contract_read_register : Symbolic.ValidContractWithFuel 10 sep_contract_read_register fun_read_register.
Proof. now apply validcontract_reflect_fuel_sound. Qed.

Lemma valid_contract_write_register : Symbolic.ValidContractWithFuel 10 sep_contract_write_register fun_write_register.
Proof. now apply validcontract_reflect_fuel_sound. Qed.

Lemma valid_contract_read_indexed : Symbolic.ValidContractWithFuel 10 sep_contract_read_indexed fun_read_indexed.
Proof. now apply validcontract_reflect_fuel_sound. Qed.

Lemma valid_contract_read_indirect : Symbolic.ValidContractWithFuel 10 sep_contract_read_indirect fun_read_indirect.
Proof. now apply validcontract_reflect_fuel_sound. Qed.

Lemma valid_contract_read_autoincrement : Symbolic.ValidContractWithFuel 10 sep_contract_read_autoincrement fun_read_autoincrement.
Proof.
  symbolic_simpl.
  repeat split; subst.
  - exfalso. unfold puntrusted in *. destruct (bv.unsigned_bounds v).
    destruct (bv.unsigned_add_view [bv [16] 0x2] v); cbn in *; lia.
  - exfalso. unfold puntrusted in *. destruct (bv.unsigned_bounds v).
    destruct (bv.unsigned_add_view [bv [16] 0x1] v); cbn in *; lia.
Qed.

Lemma valid_contract_write_indexed : Symbolic.ValidContractWithFuel 10 sep_contract_write_indexed fun_write_indexed.
Proof. now apply validcontract_reflect_fuel_sound. Qed.

Lemma valid_contract_execute_move : Symbolic.ValidContractWithFuel 10 sep_contract_execute_move fun_execute.
Proof. now apply validcontract_reflect_fuel_sound. Qed.

Lemma valid_contract_execute_jump : Symbolic.ValidContractWithFuel 10 sep_contract_execute_jump fun_execute.
Proof. now apply validcontract_reflect_fuel_sound. Qed.

Lemma valid_contract_execute_call : Symbolic.ValidContractWithFuel 10 sep_contract_execute_call fun_execute.
Proof. now apply validcontract_reflect_fuel_sound. Qed.
