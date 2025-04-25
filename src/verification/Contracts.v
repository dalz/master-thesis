From Coq Require Import
  Lists.List
  Strings.String
  ZArith.

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

Module Import MSP430Specification <: Specification MSP430Base MSP430Signature MSP430Program.
  Include SpecificationMixin MSP430Base MSP430Signature MSP430Program.

  Definition SepContractFun {Δ τ} (f : Fun Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepContractFunX {Δ τ} (f : FunX Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepLemma {Δ} (f : Lem Δ) : Type :=
    Lemma Δ.

  Section ContractDefKit.
    (* Local Notation "x + y" := (term_binop bop.plus x y). *)
    Local Notation "x ++ y" := (term_binop (@bop.bvapp _ 8 8) x y).

    Local Notation "r m↦ v" := (asn.chunk (chunk_user ptstomem [r; v])) (at level 70).

    Local Notation inc x :=
      (term_unop uop.get_slice_int
         (term_binop bop.plus
            (term_unop uop.unsigned (term_var x))
            (term_val ty.int 1))).

    Local Notation match_bw x b w :=
      (asn.match_enum Ebw x
         (fun bw => match bw with
                    | BYTE_INSTRUCTION => b
                    | WORD_INSTRUCTION => w
                    end)).

    Local Notation asn_accessible_addresses pc ipectl segb1 segb2 :=
      (asn.chunk (chunk_user accessible_addresses
                    [ term_var pc
                    ; term_var ipectl
                    ; term_var segb1
                    ; term_var segb2 ])).

    Local Notation asn_accessible_addresses_without pc ipectl segb1 segb2 addr :=
      (asn.chunk (chunk_user accessible_addresses_without
                    [ term_var pc
                    ; term_var ipectl
                    ; term_var segb1
                    ; term_var segb2
                    ; term_var addr])).

    (* Predicates *)

    Definition asn_mpu_pwd_correct {Σ} (mpuctl0 : Term Σ ty.wordBits) : Assertion Σ :=
      asn.formula
        (formula_relop bop.eq
           (term_vector_subrange 8 8 mpuctl0)
           (term_val (ty.bvec 8) [bv 0x96])).

    Definition asn_ipe_unlocked {Σ} (ipectl : Term Σ ty.wordBits) : Assertion Σ :=
      asn.formula
        (formula_relop bop.eq
           (term_vector_subrange 7 1 ipectl)
           (term_val (ty.bvec 1) [bv 0x0])).

    Definition word_times_16 {Σ} (w : Term Σ ty.wordBits) : Term Σ ty.int :=
      (term_binop bop.times
         (term_unsigned w)
         (term_val ty.int 16)).

    Definition term_plus {Σ} (m : Z) (n : Term Σ ty.int) : Term Σ ty.int :=
      (term_binop bop.plus n (term_val ty.int m)).

    Definition term_word_plus {Σ} (m : Z) (n : Term Σ ty.int) : Term Σ ty.Address :=
      term_get_slice_int (term_plus m n).

    Definition asn_ipe_entry_point {Σ}
      (segb1 addr : Term Σ ty.wordBits)
      : Assertion Σ
    :=
      asn.formula
        (formula_relop bop.eq
           (term_plus 8 (word_times_16 segb1))
           (term_unsigned addr)).

    Definition asn_not_in_ipe_segment {Σ}
      (segb1 segb2 addr : Term Σ ty.wordBits)
      : Assertion Σ
    :=
      asn.formula (formula_relop bop.lt
                     (term_unsigned addr)
                     (word_times_16 segb1))
      ∨ asn.formula (formula_relop bop.le
                       (word_times_16 segb2)
                       (term_unsigned addr)).

    Definition asn_trusted {Σ}
      (ipectl segb1 segb2 pc : Term Σ ty.wordBits)
      : Assertion Σ
    :=
      asn.formula
        (formula_or

           (* either IPE disabled... *)
           (formula_relop bop.eq
              (term_vector_subrange 6 1 ipectl)
              (term_val (ty.bvec 1) [bv 0x0]))

           (* ...or PC in IPE segment except first 8 bytes
              and not an execute read in IVT or RV (9.4.1) (TODO) *)
           (formula_and
              (formula_relop bop.le
                 (term_plus 8 (word_times_16 segb1))
                 (term_unsigned pc))
              (formula_relop bop.lt
                 (term_unsigned pc)
                 (word_times_16 segb2)))).
      (*     (* not execute access in IVT or RV (9.4.1) *) *)
      (*     /\ ((Z.lt addr 0xFF80 \/ Z.le 0xFFFF addr) *)
      (*         \/ am <> X)) *)

    Definition asn_untrusted {Σ}
      (ipectl segb1 segb2 pc : Term Σ ty.wordBits)
      : Assertion Σ
    :=
      asn.formula
        (formula_and

           (* IPE enabled *)
           (formula_relop bop.eq
              (term_vector_subrange 6 1 ipectl)
              (term_val (ty.bvec 1) [bv 0x1]))

           (* PC outside IPE segment except first 8 bytes
              or execute read in IVT or RV (9.4.1) (TODO) *)
           (formula_or
              (formula_relop bop.lt
                 (term_unsigned pc)
                 (term_plus 8 (word_times_16 segb1)))
              (formula_relop bop.le
                 (word_times_16 segb2)
                 (term_unsigned pc)))).
      (*     (* not execute access in IVT or RV (9.4.1) *) *)
      (*     /\ ((Z.lt addr 0xFF80 \/ Z.le 0xFFFF addr) *)
      (*         \/ am <> X)) *)

    Definition asn_access_allowed {Σ}
      (ipectl segb1 segb2 : Term Σ ty.wordBits)
      (am : Term Σ (ty.enum Eaccess_mode))
      (pc addr : Term Σ ty.wordBits)
      : Assertion Σ
    :=
      asn_not_in_ipe_segment segb1 segb2 addr

      ∨ (am = term_enum Eaccess_mode X
         ∗ asn_ipe_entry_point segb1 addr)

      ∨ (am = term_enum Eaccess_mode X
         ∗ asn.formula (formula_relop bop.lt
                          (term_unsigned pc)
                          (term_plus 8 (word_times_16 segb1)))
         ∗ pc = addr)

      (* XXX ∨ asn_trusted ipectl segb1 segb2 pc *).

    Definition asn_exist_mpu_registers {Σ} : Assertion Σ :=
        ∃ "MPUCTL0_reg"    , MPUCTL0_reg    ↦ term_var "MPUCTL0_reg"
      ∗ ∃ "MPUCTL1_reg"    , MPUCTL1_reg    ↦ term_var "MPUCTL1_reg"
      ∗ ∃ "MPUSEGB2_reg"   , MPUSEGB2_reg   ↦ term_var "MPUSEGB2_reg"
      ∗ ∃ "MPUSEGB1_reg"   , MPUSEGB1_reg   ↦ term_var "MPUSEGB1_reg"
      ∗ ∃ "MPUSAM_reg"     , MPUSAM_reg     ↦ term_var "MPUSAM_reg"
      ∗ ∃ "MPUIPC0_reg"    , MPUIPC0_reg    ↦ term_var "MPUIPC0_reg"
      ∗ ∃ "MPUIPSEGB2_reg" , MPUIPSEGB2_reg ↦ term_var "MPUIPSEGB2_reg"
      ∗ ∃ "MPUIPSEGB1_reg" , MPUIPSEGB1_reg ↦ term_var "MPUIPSEGB1_reg".

    Definition asn_exist_registers {Σ} : Assertion Σ :=
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

    (* Lemmas *)

    Definition lemma_extract_accessible_ptsto : SepLemma extract_accessible_ptsto :=
      {| lemma_logic_variables :=
          [ "addr" :: ty.Address; "m" :: ty.enum Eaccess_mode
          ; "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc" :: ty.wordBits
          ];

        lemma_patterns := [term_var "addr"; term_var "m"];

        lemma_precondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses "pc" "ipectl" "segb1" "segb2"
          ∗ asn_access_allowed
              (term_var "ipectl") (term_var "segb1") (term_var "segb2")
              (term_var "m") (term_var "pc") (term_var "addr");

        lemma_postcondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses_without "pc" "ipectl" "segb1" "segb2" "addr"
          ∗ ∃ "v", asn.chunk (chunk_user ptstomem [term_var "addr"; term_var "v"]);
      |}.

    Definition lemma_return_accessible_ptsto : SepLemma return_accessible_ptsto :=
      {| lemma_logic_variables :=
          [ "addr" :: ty.Address
          ; "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc" :: ty.wordBits
          ];

        lemma_patterns := [term_var "addr"];

        lemma_precondition :=
            asn_accessible_addresses_without "pc" "ipectl" "segb1" "segb2" "addr"
          ∗ ∃ "v", asn.chunk (chunk_user ptstomem [term_var "addr"; term_var "v"]);

        lemma_postcondition :=
          asn_accessible_addresses "pc" "ipectl" "segb1" "segb2";
      |}.

    Definition lemma_change_accessible_pc : SepLemma change_accessible_pc :=
      {| lemma_logic_variables :=
          [ "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc_old2" :: ty.wordBits; "pc_new" :: ty.wordBits
          ];

        lemma_patterns := [term_var "pc_old2"];

        lemma_precondition :=
            PC_reg         ↦ term_var "pc_new"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

           (* ∗ asn_accessible_addresses "pc_old" "ipectl" "segb1" "segb2" *)

          (* ∗ asn_access_allowed *)
          (*     (term_var "ipectl") (term_var "segb1") (term_var "segb2") *)
      (*     (term_enum Eaccess_mode X) (term_var "pc_old") (term_var "pc_new") *)

      ;


        lemma_postcondition :=
            PC_reg         ↦ term_var "pc_new"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses "pc_new" "ipectl" "segb1" "segb2";
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

    (* μSail function contracts *)

    (*
    Definition sep_contract_check_ipe_access :
      SepContractFun check_ipe_access :=
      {|
        sep_contract_logic_variables :=
          [ "addr"   :: ty.Address
          ; "m"      :: ty.enum Eaccess_mode
          ; "ipectl" :: ty.wordBits
          ; "segb1"  :: ty.wordBits
          ; "segb2"  :: ty.wordBits
          ; "pc"     :: ty.wordBits          ];

        sep_contract_localstore := [term_var "addr"; term_var "m"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

        sep_contract_result        := "v";
        sep_contract_postcondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"
          ∗ (asn_access_allowed
              (term_var "ipectl") (term_var "segb1") (term_var "segb2")
              (term_var "m") (term_var "pc") (term_var "addr")
             ∗ term_var "v" = term_val ty.bool true
             ∨ term_var "v" = term_val ty.bool false); (* XXX maybe needs asn_not_access_allowed? *)
      |}. *)

    Definition sep_contract_check_byte_access :
      SepContractFun check_byte_access :=
      {|
        sep_contract_logic_variables :=
          [ "addr"   :: ty.Address
          ; "m"      :: ty.enum Eaccess_mode
          ; "ipectl" :: ty.wordBits
          ; "segb1"  :: ty.wordBits
          ; "segb2"  :: ty.wordBits
          ; "pc"     :: ty.wordBits          ];

        sep_contract_localstore := [term_var "addr"; term_var "m"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2";

        sep_contract_result        := "v";
        sep_contract_postcondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"
          ∗ asn_access_allowed
              (term_var "ipectl") (term_var "segb1") (term_var "segb2")
              (term_var "m") (term_var "pc") (term_var "addr");
      |}.

    Definition sep_contract_read_mem_aux :
      SepContractFun read_mem_aux :=
      {|
        sep_contract_logic_variables :=
          [ "bw" :: ty.enum Ebw; "addr" :: ty.Address; "m" :: ty.enum Eaccess_mode
          ; "ipectl" :: ty.wordBits; "segb1"  :: ty.wordBits; "segb2"  :: ty.wordBits
          ; "pc" :: ty.wordBits
          ];

        sep_contract_localstore := [term_var "bw"; term_var "addr"; term_var "m"];

        sep_contract_precondition := ⊤;
            (* PC_reg         ↦ term_var "pc" *)
          (* ∗ MPUIPC0_reg    ↦ term_var "ipectl" *)
          (* ∗ MPUIPSEGB1_reg ↦ term_var "segb1" *)
          (* ∗ MPUIPSEGB2_reg ↦ term_var "segb2" *)

          (* ∗ asn_accessible_addresses "pc" "ipectl" "segb1" "segb2"; *)

        sep_contract_result        := "v";
        sep_contract_postcondition :=
            ∃ "u", term_var "v" = term_var "u"

          ∗ PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_access_allowed
              (term_var "ipectl") (term_var "segb1") (term_var "segb2")
              (term_var "m") (term_var "pc") (term_var "addr")

          ∗ asn_accessible_addresses "pc" "ipectl" "segb1" "segb2";
      |}.

    Definition sep_contract_set_pc :
      SepContractFun setPC :=
      {|
        sep_contract_logic_variables :=
          [ "mpuctl0" :: ty.wordBits; "ipectl" :: ty.wordBits
          ; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc" :: ty.wordBits; "pc_new" :: ty.wordBits ];

        sep_contract_localstore := [term_var "pc_new"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUCTL0_reg    ↦ term_var "mpuctl0"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_untrusted
              (term_var "ipectl") (term_var "segb1")
              (term_var "segb2") (term_var "pc");

        sep_contract_result          := "u";
        sep_contract_postcondition   :=
            term_var "u" = term_val ty.unit tt

          ∗ MPUCTL0_reg    ↦ term_var "mpuctl0"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ ∃ "pc_new",
            ( PC_reg ↦ term_var "pc_new"

            ∗ asn_access_allowed
                (term_var "ipectl") (term_var "segb1") (term_var "segb2")
                (term_enum Eaccess_mode X) (term_var "pc") (term_var "pc_new"));
      |}.

    Definition sep_contract_inc_pc :
      SepContractFun incPC :=
      {|
        sep_contract_logic_variables :=
          [ "mpuctl0" :: ty.wordBits; "ipectl" :: ty.wordBits
          ; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc_old" :: ty.wordBits; "pc_new" :: ty.wordBits
          ; "u" :: ty.unit ];

        sep_contract_localstore := [ term_var "u" ];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc_old"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_untrusted
              (term_var "ipectl") (term_var "segb1")
              (term_var "segb2") (term_var "pc_old")

          ∗ asn_accessible_addresses "pc_old" "ipectl" "segb1" "segb2";

        sep_contract_result          := "u";
        sep_contract_postcondition   :=
            term_var "u" = term_val ty.unit tt

          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ ∃ "pc_new",
            ( term_var "pc_new" = term_word_plus 2 (term_unsigned (term_var "pc_old"))

            ∗ PC_reg ↦ term_var "pc_new"

          (*   (* TODO useful? *)
          (*   ∗ asn_access_allowed *)
          (*       (term_var "ipectl") (term_var "segb1") (term_var "segb2") *)
          (*       (term_enum Eaccess_mode X) (term_var "pc_old") (term_var "pc_new")) *) *)

            ∗ asn_accessible_addresses "pc_new" "ipectl" "segb1" "segb2");
      |}.

    Definition sep_contract_fetch :
    SepContractFun fetch :=
    {|
      sep_contract_logic_variables :=
        [ "mpuctl0" :: ty.wordBits; "ipectl" :: ty.wordBits
        ; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
        ; "pc" :: ty.wordBits; "pc_new" :: ty.wordBits
        ; "u" :: ty.unit ];

      sep_contract_localstore := [ term_var "u" ];

      sep_contract_precondition :=
          PC_reg         ↦ term_var "pc"
        ∗ MPUCTL0_reg    ↦ term_var "mpuctl0"
        ∗ MPUIPC0_reg    ↦ term_var "ipectl"
        ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
        ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

        ∗ asn_untrusted
            (term_var "ipectl") (term_var "segb1")
            (term_var "segb2") (term_var "pc")

        ∗ asn_accessible_addresses "pc" "ipectl" "segb1" "segb2";

      sep_contract_result          := "v";
      sep_contract_postcondition   :=
          MPUCTL0_reg    ↦ term_var "mpuctl0"
        ∗ MPUIPC0_reg    ↦ term_var "ipectl"
        ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
        ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

        ∗ ∃ "pc_new",
          ( term_var "pc_new" = term_word_plus 2 (term_unsigned (term_var "pc"))

          ∗ PC_reg ↦ term_var "pc_new"

          (* ∗ asn_access_allowed *)
          (*     (term_var "ipectl") (term_var "segb1") (term_var "segb2") *)
          (*     (term_enum Eaccess_mode X) (term_var "pc") (term_var "pc_new") *)

          (* questo è nell'heap ma aggiungendolo viene fuori False... *)
          ∗ (asn.chunk (chunk_user accessible_addresses
              [ (term_word_plus 2 (term_unsigned (term_var "pc")))
              ; term_var "ipectl"
              ; term_var "segb1"
              ; term_var "segb2" ]))
          (* ∗ asn_accessible_addresses "pc_new" "ipectl" "segb1" "segb2" *)
);
    |}.

    Definition sep_contract_read_indexed : SepContractFun read_indexed :=
      {|
        sep_contract_logic_variables :=
          [ "mpuctl0" :: ty.wordBits; "ipectl" :: ty.wordBits
          ; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc" :: ty.wordBits
          ; "bw" :: ty.enum Ebw; "reg" :: ty.enum Eregister; "am" :: ty.enum Eam
          ];

        sep_contract_localstore := [term_var "bw"; term_var "reg"];

        sep_contract_precondition :=
            asn_exist_registers

          ∗ PC_reg         ↦ term_var "pc"
          ∗ MPUCTL0_reg    ↦ term_var "mpuctl0"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses "pc" "ipectl" "segb1" "segb2"

          ∗ asn_untrusted
              (term_var "ipectl") (term_var "segb1")
              (term_var "segb2") (term_var "pc")

          ∗ term_var "bw" = term_enum Ebw BYTE_INSTRUCTION
          ∗ term_var "reg" = term_enum Eregister SRCG1 (* XXX R4 *)
          ∗ term_var "am" = term_enum Eam INDEXED_MODE;

        sep_contract_result          := "v";
        sep_contract_postcondition   := ⊤
          (*   asn_exist_registers *)
          (* ∗ PC_reg         ↦ term_word_plus 2 (term_unsigned (term_var "pc")) *)
          (* ∗ MPUCTL0_reg    ↦ term_var "mpuctl0" *)
          (* ∗ MPUIPC0_reg    ↦ term_var "ipectl" *)
          (* ∗ MPUIPSEGB1_reg ↦ term_var "segb1" *)
          (* ∗ MPUIPSEGB2_reg ↦ term_var "segb2" *)
          (* ∗ asn_accessible_addresses "pc" "ipectl" "segb1" "segb2" *); (* XXX pc +2 *)
      |}.

    Definition sep_contract_read_mpu_reg_byte : SepContractFun read_mpu_reg_byte :=
      {|
        sep_contract_logic_variables := ["addr" :: ty.Address];
        sep_contract_localstore := [term_var "addr"];
        sep_contract_precondition := asn_exist_mpu_registers;
        sep_contract_result := "v";
        sep_contract_postcondition := asn_exist_mpu_registers;
      |}.


    Definition sep_contract_execute_move : SepContractFun execute :=
      {|
        sep_contract_logic_variables :=
          [ "mpuctl0" :: ty.wordBits; "ipectl" :: ty.wordBits
          ; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc" :: ty.wordBits
          ; "instr" :: ty.union Uast
          ];

        sep_contract_localstore := [term_var "instr"];

        sep_contract_precondition :=
            asn_exist_registers

          ∗ PC_reg         ↦ term_var "pc"
          ∗ MPUCTL0_reg    ↦ term_var "mpuctl0"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses "pc" "ipectl" "segb1" "segb2"

          ∗ asn_untrusted
              (term_var "ipectl") (term_var "segb1")
              (term_var "segb2") (term_var "pc")

          ∗ term_var "instr" =
              term_union Uast Kdoubleop
                (term_val (unionk_ty Uast Kdoubleop)
                   (tt, MOV, BYTE_INSTRUCTION, R4, INDEXED_MODE, R5, REGISTER_MODE));

        sep_contract_result          := "u";
        sep_contract_postcondition   :=
            term_var "u" = term_val ty.unit tt
          ∗ asn_exist_registers

          ∗ PC_reg         ↦ term_var "pc"
          ∗ MPUCTL0_reg    ↦ term_var "mpuctl0"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_accessible_addresses "pc" "ipectl" "segb1" "segb2";
      |}.

    Definition sep_contract_execute_jump :
      SepContractFun execute :=
      {|
        sep_contract_logic_variables :=
          [ "mpuctl0" :: ty.wordBits; "ipectl" :: ty.wordBits
          ; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc" :: ty.wordBits
          ; "instr" :: ty.union Uast
          ; "jump_arg" :: unionk_ty Uast Kjump ];

        sep_contract_localstore := [term_var "instr"];

        sep_contract_precondition :=
            asn_exist_registers

          ∗ PC_reg         ↦ term_var "pc"
          ∗ MPUCTL0_reg    ↦ term_var "mpuctl0"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ asn_untrusted
              (term_var "ipectl") (term_var "segb1")
              (term_var "segb2") (term_var "pc")

          ∗ term_var "instr" = term_union Uast Kjump (term_var "jump_arg");

        sep_contract_result          := "u";
        sep_contract_postcondition   :=
            term_var "u" = term_val ty.unit tt
          ∗ asn_exist_registers

          ∗ MPUCTL0_reg    ↦ term_var "mpuctl0"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ ∃ "pc_new",
            ( PC_reg ↦ term_var "pc_new"

            ∗ asn_access_allowed
                (term_var "ipectl") (term_var "segb1") (term_var "segb2")
                (term_enum Eaccess_mode X) (term_var "pc") (term_var "pc_new"));
      |}.

    Definition sep_contract_execute :
      SepContractFun execute :=
      {|
        sep_contract_logic_variables :=
          [ "mpuctl0" :: ty.wordBits; "ipectl" :: ty.wordBits
          ; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "pc" :: ty.wordBits
          ; "instr" :: ty.union Uast ];

        sep_contract_localstore := [term_var "instr"];

        sep_contract_precondition :=
            PC_reg ↦ term_var "pc"
          ∗ MPUCTL0_reg    ↦ term_var "mpuctl0"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"
          ∗ asn_accessible_addresses "pc" "ipectl" "segb1" "segb2";

        sep_contract_result          := "u";
        sep_contract_postcondition   :=
            term_var "u" = term_val ty.unit tt

            (* TODO if password is wrong then only it is allowed to change *)
          ∗ (∃ "mpuctl0_new", MPUCTL0_reg ↦ term_var "mpuctl0_new")

          ∗ ∃ "ipectl_new", ∃ "segb1_new", ∃ "segb2_new", ∃ "pc_new",
            ( MPUIPC0_reg    ↦ term_var "ipectl_new"
            ∗ MPUIPSEGB1_reg ↦ term_var "segb1_new"
            ∗ MPUIPSEGB2_reg ↦ term_var "segb2_new"

              (* IPE control registers can change if the password is correct
                 and they are not locked TODO and they are not protected by IPE? *)
            ∗ (   asn_mpu_pwd_correct (term_var "mpuctl0")
                ∗ asn_ipe_unlocked (term_var "ipectl")

              ∨ (* otherwise they must stay the same *)
                  term_var "ipectl_new" = term_var "ipectl"
                ∗ term_var "segb1_new"  = term_var "segb1"
                ∗ term_var "segb2_new"  = term_var "segb2"
              )

            ∗ PC_reg ↦ term_var "pc_new"

            ∗ (* jumps to untrusted sections are always allowed *)
              ( asn_not_in_ipe_segment
                  (term_var "segb1") (term_var "segb2") (term_var "pc_new")

                (* arbitrary jumps into the IPE segment are allowed only from the IPE segment *)
              ∨ asn_access_allowed
                  (term_var "ipectl_new") (term_var "segb1_new") (term_var "segb2_new")
                  (term_enum Eaccess_mode X) (term_var "pc") (term_var "pc_new")

                (* untrusted code can only jump to the entry point *)
              ∨ asn_ipe_entry_point (term_var "segb1_new") (term_var "pc_new")
              )

            ∗ asn_accessible_addresses "pc_new" "ipectl" "segb1_new" "segb2_new");
      |}.

    (* The following maps μSail function names to their contracts. *)
    Definition CEnv : SepContractEnv :=
      fun Δ τ f =>
        match f with
        | read_mem_aux => Some sep_contract_read_mem_aux
        | read_mpu_reg_byte => Some sep_contract_read_mpu_reg_byte
        | check_byte_access => Some sep_contract_check_byte_access
        | setPC => Some sep_contract_set_pc
        | incPC => Some sep_contract_inc_pc

          (* | execute => Some sep_contract_execute *)
        | _ => None
        end.

    (* And this definition maps foreign functions to their contracts. *)
    Definition CEnvEx : SepContractEnvEx :=
      fun Δ τ f =>
        match f with
        | @undefined_bitvector n => sep_contract_undefined_bitvector n
        | read_ram => sep_contract_read_ram
        | write_ram => sep_contract_write_ram
        end.

    (* And finally a mapping from ghost lemmas to the entailments they encode. *)
    Definition LEnv : LemmaEnv :=
      fun Δ l =>
        match l with
        | extract_accessible_ptsto => lemma_extract_accessible_ptsto
        | return_accessible_ptsto => lemma_return_accessible_ptsto
        | change_accessible_pc => lemma_change_accessible_pc
        end.
  End ContractDefKit.
End MSP430Specification.

(*** VERIFICATION ***)

Import MSP430Specification.
Import SymProp.notations.
(* Import Erasure.notations. *)

Module MSP430Executor :=
  MakeExecutor MSP430Base MSP430Signature MSP430Program MSP430Specification.

Import MSP430Executor.
Import MSP430Executor.Symbolic.

Ltac symbolic_simpl_reflect :=
  apply validcontract_reflect_sound;
  compute;
  constructor;
  cbn.

Ltac symbolic_simpl_fuel :=
  apply validcontract_reflect_fuel_sound;
  compute;
  constructor;
  cbn.

Ltac symbolic_simpl_erasure :=
  apply validcontract_with_erasure_sound;
  compute;
  constructor;
  cbn.
(*
Lemma valid_contract_fetch : Symbolic.ValidContract sep_contract_fetch fun_fetch.
Proof.
  compute.
  constructor.
  cbn [SymProp.safe instprop instprop_formula].
  intros.

  exists [bv 0]. exists [bv 0]. exists [bv 0]. exists [bv 0]. intro.
  split.

  
  intros until v5.
  intros Henabled Huntrusted _.
  exists v0.
  exists v1.
  exists v2.
  exists v3.                (* v4? *)
  intro.
  repeat split.
  - intros H_pc_untrusted_left.
    exists [bv 0].
    repeat split.
    + assumption.
    + assumption.
    + 
      left.
      cbn.
      cbn in H_pc_untrusted_left.
      replace (bv.unsigned v3) with (bv.unsigned v3 + 0) by ring.
      rewrite Z.add_comm with (n := 8).
      apply Z.add_lt_mono; [assumption | reflexivity].
    +  intros ? H_pc_plus_2_unprotected ?.



  intros until v6.
  intros _ Huntrusted _.
  repeat split.
  - intros H_pc_untrusted_left.
    exists [bv 0].
    repeat split.
    + left.
      cbn.
      cbn in H_pc_untrusted_left.
      replace (bv.unsigned v3) with (bv.unsigned v3 + 0) by ring.
      rewrite Z.add_comm with (n := 8).
      apply Z.add_lt_mono; [assumption | reflexivity].
    +  intros ? H_pc_plus_2_unprotected ?.

Lemma valid_contract_read_indexed : Symbolic.ValidContractWithFuel 100 sep_contract_read_indexed fun_read_indexed.
Proof.
  compute.
  constructor.
  cbn [SymProp.safe instprop instprop_formula].
  intros until v20.
  intros _ Huntrusted _.

  repeat split.
  - intros H_pc_untrusted_left.
    exists [bv 0].
    repeat split.
    + left.
      cbn.
      cbn in H_pc_untrusted_left.
      replace (bv.unsigned v3) with (bv.unsigned v3 + 0) by ring.
      rewrite Z.add_comm with (n := 8).
      apply Z.add_lt_mono; [assumption | reflexivity].
    +  intros ? H_pc_plus_2_unprotected ?.



    intros ? H_pc_plus_2_unprotected ?.

-




  exists [bv [16] 4242].
  exists [bv [16] 3131].
  exists [bv [16] 9797].
  exists [bv [16] 5656].
  intros.
  repeat split;
    try exact [bv 0];
    intros ? H_pc_plus_2_unprotected H;
    exists [bv [16] 1111];
    exists [bv [16] 2222];
    exists [bv [16] 3333];
    exists [bv [16] 4444];
    intros;
    cbn;
    (split; [|reflexivity]);
    unfold bv.add;
    cbn;
    rewrite <-bv.of_Z_add, <-bv.of_N_add, bv.of_Z_unsigned, bv.of_N_bin, bv.add_comm;
    reflexivity.
Qed.

Lemma valid_contract_execute_move : Symbolic.ValidContractWithFuel 100 sep_contract_execute_move fun_execute.
Proof.
  compute.

  *)


Lemma valid_contract_check_byte_access : Symbolic.ValidContractReflect sep_contract_check_byte_access fun_check_byte_access.
Proof. Admitted.

Lemma valid_contract_read_mem_aux : Symbolic.ValidContractWithFuel 100 sep_contract_read_mem_aux fun_read_mem_aux.
Proof. Admitted.

Lemma valid_contract_execute_set_pc : Symbolic.ValidContract sep_contract_set_pc fun_setPC.
Proof. symbolic_simpl_reflect. Qed.

Lemma valid_contract_execute_inc_pc : Symbolic.ValidContract sep_contract_inc_pc fun_incPC.
Proof.
  compute.
  constructor.
  cbn [SymProp.safe instprop instprop_formula].

  intros. split. split. intros.

  symbolic_simpl_reflect. Qed.

Lemma valid_contract_execute_jump : Symbolic.ValidContractWithFuel 100 sep_contract_execute_jump fun_execute.
Proof.
  apply validcontract_reflect_fuel_sound.
  compute.
  constructor.
  cbn [SymProp.safe instprop instprop_formula].
  intros until v20.
  intros _ Hpc;
    repeat split;
    try intros _;
    try apply Hpc;
    (destruct Hpc as [Hpc | Hpc];
     [right | left]; right;
     rewrite rightid_and_true; apply Hpc).
Qed.
