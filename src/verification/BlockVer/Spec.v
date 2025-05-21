From Coq Require Import
     ZArith.ZArith
     Strings.String
     Lists.List.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Iris.Instance
     Iris.Base
     Notations
     Bitvector
     Sep.Hoare
     Specification
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.SymbolicExecutor
     MicroSail.RefineExecutor
     MicroSail.Soundness.

From MSP430 Require Import Machine Sig.

Import MSP430Program.
Import ListNotations.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import bv.notations.

Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Module Assembly.
  Definition MPUIPC0_addr {Σ} : Term Σ _ := term_val ty.Address [bv 0x05AA].
  Definition MPUIPSEGB2_addr {Σ} : Term Σ _ := term_val ty.Address [bv [16] 0x05AC].
  Definition MPUIPSEGB1_addr {Σ} : Term Σ _ := term_val ty.Address [bv [16] 0x05AE].

  Inductive ast_with_args :=
  | I0 (i : ast)
  | I1 (i : ast) (a : bv 16)
  | I2 (i : ast) (a : bv 16) (b : bv 16).

  Definition instr_without_args i :=
    match i with
      I0 i | I1 i _ | I2 i _ _ => i
    end.

  Definition add_rr rs rd :=
    I0 (DOUBLEOP ADD WORD_INSTRUCTION rs REGISTER_MODE rd REGISTER_MODE).

  Definition tst_m r :=
    I0 (DOUBLEOP CMP WORD_INSTRUCTION CG2 REGISTER_MODE r INDIRECT_REGISTER_MODE).

  Definition clr_m r :=
    I0 (DOUBLEOP MOV WORD_INSTRUCTION CG2 REGISTER_MODE r INDIRECT_REGISTER_MODE).

  Definition cmp_rm rs rd :=
    I0 (DOUBLEOP CMP WORD_INSTRUCTION rs REGISTER_MODE rd INDIRECT_REGISTER_MODE).

  Definition cmp_mr rs rd :=
    I0 (DOUBLEOP CMP WORD_INSTRUCTION rs INDIRECT_REGISTER_MODE rd REGISTER_MODE).

  Definition mov_rr rs rd :=
    I0 (DOUBLEOP MOV WORD_INSTRUCTION rs REGISTER_MODE rd REGISTER_MODE).

  Definition mov_mm rs rd :=
    I0 (DOUBLEOP MOV WORD_INSTRUCTION rs INDIRECT_REGISTER_MODE rd INDIRECT_REGISTER_MODE).

  Definition mov_mr rs rd :=
    I0 (DOUBLEOP MOV WORD_INSTRUCTION rs INDIRECT_REGISTER_MODE rd REGISTER_MODE).

  Definition mov_im rs i rd :=
    I1
      (DOUBLEOP MOV WORD_INSTRUCTION rs INDEXED_MODE rd INDIRECT_REGISTER_MODE)
      i.

  Definition mov_ir rs i rd :=
    I1
      (DOUBLEOP MOV WORD_INSTRUCTION rs INDEXED_MODE rd REGISTER_MODE)
      i.

  Definition xor_ar rs rd :=
    I0 (DOUBLEOP XOR WORD_INSTRUCTION rs INDIRECT_AUTOINCREMENT_MODE rd REGISTER_MODE).

  Definition jump kind off :=
    I0 (JUMP kind off).

End Assembly.

Module Utils.
  Import asn.notations.
  Import Assembly.

  Notation "a @ b" := (term_binop (@bop.bvapp _ 8 8) a b) (at level 60).
  Notation "v +' n" :=  (term_binop bop.bvadd v (term_val ty.wordBits [bv n])) (at level 50).

  Notation "a m↦ v" := (asn.chunk (chunk_user ptstomem [a; v])) (at level 70).
  Notation "a i↦ i" := (asn.chunk (chunk_user ptstoinstr [a; i])) (at level 70).
  Notation "w ≡ i" := (asn.chunk (chunk_user encodes_instr [w; i])) (at level 70).

  Notation asn_accessible_addresses segb1 segb2 :=
    (asn.chunk_angelic (chunk_user accessible_addresses
                          [term_var segb1; term_var segb2])).

  Notation asn_accessible_addresses_without segb1 segb2 addr :=
    (asn.chunk_angelic (chunk_user accessible_addresses_without
                          [term_var segb1; term_var segb2; term_var addr])).

  Definition term_plus {Σ} (m : Z) (n : Term Σ ty.int) : Term Σ ty.int :=
    (term_binop bop.plus n (term_val ty.int m)).

  Definition word_times_16 {Σ} (w : Term Σ ty.wordBits) : Term Σ ty.int :=
    (term_binop bop.times
       (term_unsigned w)
       (term_val ty.int 16%Z)).

  Definition high {Σ} (v : Term Σ (ty.bvec 16)) : Term Σ _ := term_vector_subrange 0 8 v.
  Definition low {Σ} (v : Term Σ (ty.bvec 16)) : Term Σ _ := term_vector_subrange 8 8 v.

  Definition bor1 {Σ} (v : Term Σ ty.wordBits) : Term Σ _ :=
    term_binop bop.bvor v (term_val ty.wordBits [bv 1]).

  Definition asn_word_aligned {Σ} (addr : Term Σ ty.Address) : Assertion Σ :=
    addr = term_binop bop.bvand addr (term_val ty.Address [bv 0xfffe]).

  Definition asn_ptsto_word {Σ}
    (addr : Term Σ ty.Address)
    (bl bh : Term Σ ty.byteBits)
    : Assertion Σ
  :=
      addr m↦ bl
    ∗ bor1 addr m↦ bh.

  Notation "a w↦ l h" := (asn_ptsto_word a l h) (at level 70).

  Definition asn_ipe_entry_point {Σ}
      (segb1 addr : Term Σ ty.wordBits)
      : Assertion Σ
    :=
      asn.formula
        (formula_relop bop.eq
           (term_plus 8 (word_times_16 segb1))
           (term_unsigned addr)).

  Definition asn_not_mpu_reg_addr {Σ} (addr : Term Σ ty.Address) : Assertion Σ :=
    term_unsigned addr < term_unsigned MPUIPC0_addr
    ∨ term_unsigned (MPUIPSEGB1_addr +' 2) <= term_unsigned addr.

  Definition asn_mpu_registers {Σ} : Assertion Σ :=
      ∃ "MPUCTL0_reg"    , MPUCTL0_reg    ↦ term_var "MPUCTL0_reg"
    ∗ ∃ "MPUCTL1_reg"    , MPUCTL1_reg    ↦ term_var "MPUCTL1_reg"
    ∗ ∃ "MPUSEGB2_reg"   , MPUSEGB2_reg   ↦ term_var "MPUSEGB2_reg"
    ∗ ∃ "MPUSEGB1_reg"   , MPUSEGB1_reg   ↦ term_var "MPUSEGB1_reg"
    ∗ ∃ "MPUSAM_reg"     , MPUSAM_reg     ↦ term_var "MPUSAM_reg".
End Utils.

Module MSP430BlockVerifSpec <: Specification MSP430Base MSP430Signature MSP430Program.
  Include SpecificationMixin MSP430Base MSP430Signature MSP430Program.

  Import asn.notations.
  Import Assembly.
  Import Utils.

  Definition SepContractFun {Δ τ} (f : Fun Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepContractFunX {Δ τ} (f : FunX Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepLemma {Δ} (f : Lem Δ) : Type :=
    Lemma Δ.

  (* Lemmas *)

  Definition lemma_extract_accessible_ptsto : SepLemma extract_accessible_ptsto :=
    {|
      lemma_logic_variables := ["addr" :: ty.Address];
      lemma_patterns := [term_var "addr"];
      lemma_precondition := ⊤;
      lemma_postcondition := ⊤;
    |}.

  Definition lemma_return_accessible_ptsto : SepLemma return_accessible_ptsto :=
    {|
      lemma_logic_variables := ["addr" :: ty.Address];
      lemma_patterns := [term_var "addr"];
      lemma_precondition := ⊤;
      lemma_postcondition := ⊤;
    |}.

  (* useless for now, should be called in fetch, for verification *)
  Definition lemma_open_ptsto_instr : SepLemma open_ptsto_instr :=
    {|
      lemma_logic_variables := ["addr" :: ty.wordBits; "id" :: ty.union Uinstr_or_data];
      lemma_patterns        := [term_var "addr"];
      lemma_precondition    := term_var "addr" i↦ term_var "id";
      lemma_postcondition   :=
        ∃ "bl", ∃ "bh",
        ( asn_ptsto_word (term_var "addr") (term_var "bl") (term_var "bh")
        ∗ ( ∃ "i", (term_var "id" = term_union Uinstr_or_data Ki (term_var "i")
                    ∗ term_var "bh" @ term_var "bl" ≡ term_var "i")
          ∨ ∃ "d", (term_var "id" = term_union Uinstr_or_data Kd (term_var "d")
                    ∗ term_var "bh" @ term_var "bl" = term_var "d")))
    |}.

  Definition lemma_close_ptsto_instr : SepLemma close_ptsto_instr :=
    {|
      lemma_logic_variables :=
        [ "addr" :: ty.wordBits; "id" :: ty.union Uinstr_or_data ];

      lemma_patterns := [term_var "addr"];

      lemma_precondition :=
        ∃ "bl", ∃ "bh",
        ( asn_ptsto_word (term_var "addr") (term_var "bl") (term_var "bh")
        ∗ ( ∃ "i", (term_var "id" = term_union Uinstr_or_data Ki (term_var "i")
                    ∗ term_var "bh" @ term_var "bl" ≡ term_var "i")
          ∨ ∃ "d", (term_var "id" = term_union Uinstr_or_data Kd (term_var "d")
                    ∗ term_var "bh" @ term_var "bl" = term_var "d")));

      lemma_postcondition := term_var "addr" i↦ term_var "id";
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
      sep_contract_logic_variables :=
        [ "wb" :: ty.union Uwordbyte; "w" :: ty.wordBits; "i" :: ty.union Uast];
      sep_contract_localstore := [term_var "wb"];

      sep_contract_precondition    :=
          term_var "wb" = term_union Uwordbyte Kword (term_var "w")
        ∗ term_var "w" ≡ term_var "i";

      sep_contract_result          := "r";
      sep_contract_postcondition   := term_var "r" = term_var "i";
    |}.

  (* Sail function contracts *)

  (*
  Definition asn_read_mpu_reg_result {Σ}
    (ipectl segb1 segb2 addr : Term Σ ty.wordBits) (v : Term Σ ty.byteBits)
    : Assertion Σ
  :=
    ( addr = MPUIPC0_addr ∗ v = low ipectl
    ∨ addr = MPUIPC0_addr +' 1 ∗ v = high ipectl
    ∨ addr = MPUIPSEGB1_addr ∗ v = low segb1
    ∨ addr = MPUIPSEGB1_addr +' 1 ∗ v = high segb1
    ∨ addr = MPUIPSEGB2_addr ∗ v = low segb2
    ∨ addr = MPUIPSEGB2_addr +' 1 ∗ v = high segb2
    ∨ term_unsigned addr < term_unsigned MPUIPC0_addr
    ∨ term_unsigned (MPUIPSEGB1_addr +' 2) <= term_unsigned addr).

  Definition sep_contract_read_mpu_reg_byte :
    SepContractFun read_mpu_reg_byte :=
    {|
      sep_contract_logic_variables :=
        [ "addr" :: ty.Address; "ipectl" :: ty.wordBits
        ; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits ];

      sep_contract_localstore := [term_var "addr"];

      sep_contract_precondition :=
          MPUIPC0_reg    ↦ term_var "ipectl"
        ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
        ∗ MPUIPSEGB2_reg ↦ term_var "segb2"
        ∗ asn_mpu_registers;

      sep_contract_result        := "v";
      sep_contract_postcondition :=
          asn_read_mpu_reg_result
            (term_var "ipectl") (term_var "segb1") (term_var "segb2")
            (term_var "addr") (term_var "v")

        ∗ MPUIPC0_reg    ↦ term_var "ipectl"
        ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
        ∗ MPUIPSEGB2_reg ↦ term_var "segb2"
        ∗ asn_mpu_registers;
    |}.
   *)

  Definition sep_contract_check_byte_access :
    SepContractFun check_byte_access :=
    {|
      sep_contract_logic_variables :=
        [ "addr" :: ty.Address; "jump" :: ty.bool
        ; "pc" :: ty.wordBits; "ipectl" :: ty.wordBits
        ; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
        ];

      sep_contract_localstore := [term_var "addr"; term_var "jump"];

      sep_contract_precondition :=
          PC_reg         ↦ term_var "pc"
        ∗ MPUIPC0_reg    ↦ term_var "ipectl"
        ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
        ∗ MPUIPSEGB2_reg ↦ term_var "segb2";

      sep_contract_result        := "v";
      sep_contract_postcondition :=
          term_var "v" = term_val ty.unit tt

        ∗ PC_reg         ↦ term_var "pc"
        ∗ MPUIPC0_reg    ↦ term_var "ipectl"
        ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
        ∗ MPUIPSEGB2_reg ↦ term_var "segb2";
    |}.

  Definition sep_contract_read_mem_aux :
      SepContractFun read_mem_aux :=
      {|
        sep_contract_logic_variables :=
          [ "bw" :: ty.enum Ebw; "addr" :: ty.Address; "pc" :: ty.wordBits
          ; "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
          ; "bl" :: ty.byteBits; "bh" :: ty.byteBits ];

        sep_contract_localstore := [term_var "bw"; term_var "addr"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

          ∗ ( ( term_var "bw" = term_enum Ebw WORD_INSTRUCTION
              ∗ asn_ptsto_word (term_var "addr") (term_var "bl") (term_var "bh")
              (* ∗ asn_word_aligned (term_var "addr") *))
            ∨ ( term_var "bw" = term_enum Ebw BYTE_INSTRUCTION
              ∗ term_var "addr" m↦ term_var "bl"))

          (* the bootcode never reads the MPU registers *)
          ∗ asn_not_mpu_reg_addr (term_var "addr");

        sep_contract_result        := "v";
        sep_contract_postcondition :=
            ( ( term_var "bw" = term_enum Ebw WORD_INSTRUCTION
              ∗ term_var "v" = term_union Uwordbyte Kword (term_var "bh" @ term_var "bl")
              ∗ asn_ptsto_word (term_var "addr") (term_var "bl") (term_var "bh"))
            ∨ ( term_var "bw" = term_enum Ebw BYTE_INSTRUCTION
              ∗ term_var "v" = term_union Uwordbyte Kbyte (term_var "bl")
              ∗ term_var "addr" m↦ term_var "bl"))

          ∗ PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2";
      |}.

  (* Definition sep_contract_fetch : SepContractFun fetch := *)
  (*   {| *)
  (*     sep_contract_logic_variables := *)
  (*       [ "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits *)
  (*       ; "pc_old" :: ty.wordBits; "id" :: ty.union Uinstr_or_data *)
  (*       ; "u" :: ty.unit ]; *)

  (*     sep_contract_localstore := [ term_var "u" ]; *)

  (*     sep_contract_precondition := *)
  (*       term_var "pc_old" = term_val ty.wordBits [bv 0] ∗ *)
  (*         PC_reg         ↦ term_var "pc_old" *)
  (*       ∗ MPUIPC0_reg    ↦ term_var "ipectl" *)
  (*       ∗ MPUIPSEGB1_reg ↦ term_var "segb1" *)
  (*       ∗ MPUIPSEGB2_reg ↦ term_var "segb2" *)
  (*       ∗ asn_mpu_registers *)

  (*       (* ∗ asn_ipe_configured  (term_var "ipectl") *) *)
  (*       (* ∗ asn_untrusted *) *)
  (*       (*     (term_var "segb1") (term_var "segb2") (term_var "pc_old") *) *)

  (*       ∗ term_var "pc_old" i↦ term_var "id"; *)

  (*     sep_contract_result          := "v"; *)
  (*     sep_contract_postcondition   := *)
  (*         MPUIPC0_reg    ↦ term_var "ipectl" *)
  (*       ∗ MPUIPSEGB1_reg ↦ term_var "segb1" *)
  (*       ∗ MPUIPSEGB2_reg ↦ term_var "segb2" *)
  (*       (* ∗ asn_mpu_registers *) *)

  (*       (* ∗ PC_reg ↦ term_var "pc_old" +' 2 *) *)

  (*       (* ∗ term_var "pc_old" i↦ term_var "id" *) *)
  (*       (* ∗ ∃ "w", *) *)
  (*       (*   ( term_var "v" = term_union Uwordbyte Kword (term_var "w") *) *)

  (*       (*   ∗ ( ∃ "i", ( term_var "id" = term_union Uinstr_or_data Ki (term_var "i") *) *)
  (*       (*              ∗ term_var "w" ≡ term_var "i") *) *)
  (*       (*     ∨ term_var "id" = term_union Uinstr_or_data Kd (term_var "w"))) *); *)

  (*     (* encodes_instr is duplicable *) *)

  (*       (* ∗ ∃ "pc_new", *) *)
  (*       (*   ( term_var "pc_new" = term_word_plus [bv 2] (term_var "pc_old") *) *)
  (*       (*     ∗ PC_reg ↦ term_var "pc_new" *) *)
  (*       (*     ∗ asn_untrusted *) *)
  (*       (*         (term_var "segb1") (term_var "segb2") (term_var "pc_new")); *) *)
  (*   |}. *)

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | read_mem_aux => Some sep_contract_read_mem_aux
      (* | write_mpu_reg_byte => Some sep_contract_write_mpu_reg_byte *)
      | check_byte_access => Some sep_contract_check_byte_access
      (* | fetch => Some sep_contract_fetch *)
      | _ => None
      end.

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | decode => sep_contract_decode
      | read_ram => sep_contract_read_ram
      | write_ram => sep_contract_write_ram
      | @undefined_bitvector n => sep_contract_undefined_bitvector n
      end.

  Definition LEnv : LemmaEnv :=
    fun Δ l =>
      match l with
      | extract_accessible_ptsto => lemma_extract_accessible_ptsto
      | return_accessible_ptsto => lemma_return_accessible_ptsto
      | open_ptsto_instr => lemma_open_ptsto_instr
      | close_ptsto_instr => lemma_close_ptsto_instr
      end.
End MSP430BlockVerifSpec.

Module MSP430BlockVerifShalExecutor :=
  MakeShallowExecutor MSP430Base MSP430Signature MSP430Program MSP430BlockVerifSpec.
Module MSP430BlockVerifExecutor :=
  MakeExecutor MSP430Base MSP430Signature MSP430Program MSP430BlockVerifSpec.

Module RiscvPmpSpecVerif.
  Import MSP430BlockVerifSpec.
  Import MSP430BlockVerifExecutor.Symbolic.
  Import MSP430BlockVerifExecutor.

  Import ModalNotations.
  Import Erasure.notations.

  Ltac symbolic_simpl :=
    apply validcontract_with_erasure_and_fuel_sound;
    compute;
    constructor;
    simpl.

  Definition ValidContractWithFuel {Δ τ} (fuel : nat) (c : SepContract Δ τ) (body : Stm Δ τ) : Prop :=
  VerificationCondition
    ((SPureSpec.replay ( (vcgen default_config fuel c body wnil)))).
  
  Lemma valid_read_mem_aux : ValidContractWithFuel 10 sep_contract_read_mem_aux fun_read_mem_aux.
  Proof.
  vm_compute. Set Printing Depth 200. Admitted.
    (* symbolic_simpl. Admitted. *)

  Lemma valid_check_byte_access : ValidContractWithFuel 10 sep_contract_check_byte_access fun_check_byte_access.
  Proof. now symbolic_simpl. Qed.

  (* Lemma valid_execute_fetch : ValidContractWithFuel 10 sep_contract_fetch fun_fetch. *)
  (* Proof. *)
  (*   symbolic_simpl. *)
  (* Qed. *)
End RiscvPmpSpecVerif.
