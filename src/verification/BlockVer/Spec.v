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
  Inductive ast_with_args :=
  | I0 (i : ast)
  | I1 (i : ast) (a : bv 16)
  | I2 (i : ast) (a : bv 16) (b : bv 16).

  Definition instr_without_args i :=
    match i with
      I0 i | I1 i _ | I2 i _ _ => i
    end.

  Definition MOV_WRR (rs rd : Register) : ast_with_args :=
    I0 (DOUBLEOP MOV WORD_INSTRUCTION rs REGISTER_MODE rd REGISTER_MODE).

  Definition ADD_WRR (rs rd : Register) : ast_with_args :=
    I0 (DOUBLEOP ADD WORD_INSTRUCTION rs REGISTER_MODE rd REGISTER_MODE).
End Assembly.

Module MSP430BlockVerifSpec <: Specification MSP430Base MSP430Signature MSP430Program.
  Include SpecificationMixin MSP430Base MSP430Signature MSP430Program.

  Import asn.notations.

  Local Notation "a @ b" := (term_binop (@bop.bvapp _ 8 8) a b) (at level 60).
  Local Notation "v +' n" :=  (term_binop bop.bvadd v (term_val ty.wordBits [bv n])) (at level 50).

  Local Notation "a m↦ v" := (asn.chunk (chunk_user ptstomem [a; v])) (at level 70).
  Local Notation "a i↦ i" := (asn.chunk (chunk_user ptstoinstr [a; i])) (at level 70).
  Local Notation "w ≡ i" := (asn.chunk (chunk_user encodes_instr [w; i])) (at level 70).

  Local Notation asn_accessible_addresses segb1 segb2 :=
    (asn.chunk_angelic (chunk_user accessible_addresses
                          [term_var segb1; term_var segb2])).

  Local Notation asn_accessible_addresses_without segb1 segb2 addr :=
    (asn.chunk_angelic (chunk_user accessible_addresses_without
                          [term_var segb1; term_var segb2; term_var addr])).

  Definition term_plus {Σ} (m : Z) (n : Term Σ ty.int) : Term Σ ty.int :=
    (term_binop bop.plus n (term_val ty.int m)).

  Definition word_times_16 {Σ} (w : Term Σ ty.wordBits) : Term Σ ty.int :=
    (term_binop bop.times
       (term_unsigned w)
       (term_val ty.int 16%Z)).

  Definition asn_ipe_entry_point {Σ}
      (segb1 addr : Term Σ ty.wordBits)
      : Assertion Σ
    :=
      asn.formula
        (formula_relop bop.eq
           (term_plus 8 (word_times_16 segb1))
           (term_unsigned addr)).

  Definition asn_unprotected {Σ}
      (segb1 segb2 : Term Σ ty.wordBits)
      (am : Term Σ (ty.enum Eaccess_mode))
      (addr : Term Σ ty.Address)
      : Assertion Σ
    :=
        asn.formula (formula_relop bop.lt
                       (term_unsigned addr)
                       (word_times_16 segb1))
      ∨ asn.formula (formula_relop bop.le
                       (word_times_16 segb2)
                       (term_unsigned addr))

      ∨ ( am = term_enum Eaccess_mode X
        ∗ asn_ipe_entry_point segb1 addr).

  Definition asn_mpu_registers {Σ} : Assertion Σ :=
      ∃ "MPUCTL0_reg"    , MPUCTL0_reg    ↦ term_var "MPUCTL0_reg"
    ∗ ∃ "MPUCTL1_reg"    , MPUCTL1_reg    ↦ term_var "MPUCTL1_reg"
    ∗ ∃ "MPUSEGB2_reg"   , MPUSEGB2_reg   ↦ term_var "MPUSEGB2_reg"
    ∗ ∃ "MPUSEGB1_reg"   , MPUSEGB1_reg   ↦ term_var "MPUSEGB1_reg"
    ∗ ∃ "MPUSAM_reg"     , MPUSAM_reg     ↦ term_var "MPUSAM_reg".

  Definition SepContractFun {Δ τ} (f : Fun Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepContractFunX {Δ τ} (f : FunX Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepLemma {Δ} (f : Lem Δ) : Type :=
    Lemma Δ.

  (* Lemmas *)

  Definition lemma_extract_accessible_ptsto : SepLemma extract_accessible_ptsto :=
    {|
      lemma_logic_variables := ["addr" :: ty.Address; "m" :: ty.enum Eaccess_mode];
      lemma_patterns := [term_var "addr"; term_var "m"];
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

        ( ∃ "i",
            (term_var "id" = term_union Uinstr_or_data Ki (term_var "i")
             ∗ term_var "addr" m↦ term_var "bl"
             ∗ term_var "addr" m↦ term_var "bh"
             ∗ term_var "bh" @ term_var "bl" ≡ term_var "i")

        ∨

         ∃ "d",
           (term_var "id" = term_union Uinstr_or_data Kd (term_var "d")
            ∗ term_var "addr" m↦ term_var "bl"
            ∗ term_var "addr" m↦ term_var "bh"
            ∗ term_var "bh" @ term_var "bl" = term_var "d"))
    |}.

  Definition lemma_close_ptsto_instr : SepLemma close_ptsto_instr :=
    {|
      lemma_logic_variables :=
        [ "addr" :: ty.wordBits; "i" :: ty.union Uast
        ; "bl" :: ty.byteBits; "bh" :: ty.byteBits
        ];

      lemma_patterns := [term_var "addr"(* ; term_var "w" *)];

      lemma_precondition := ⊤;
        (*   term_var "addr" m↦ term_var "bl" *)
        (* ∗ term_binop bop.bvadd (term_var "addr") (term_val ty.wordBits [bv 1]) *)
        (*     m↦ term_var "bh" *)
        (* ∗ term_binop (@bop.bvapp _ 8 8) (term_var "bh") (term_var "bl") *)
        (*     ≡ term_var "i"; *)

      lemma_postcondition := (* term_var "addr" i↦ term_var "i" *) ⊤;
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

  (* Sail function contracts *)

  Definition sep_contract_fetch : SepContractFun fetch :=
    {|
      sep_contract_logic_variables :=
        [ "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits
        ; "pc_old" :: ty.wordBits; "id" :: ty.union Uinstr_or_data
        ; "u" :: ty.unit ];

      sep_contract_localstore := [ term_var "u" ];

      sep_contract_precondition :=
          PC_reg         ↦ term_var "pc_old"
        ∗ MPUIPC0_reg    ↦ term_var "ipectl"
        ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
        ∗ MPUIPSEGB2_reg ↦ term_var "segb2"
        ∗ asn_mpu_registers

        (* ∗ asn_ipe_configured  (term_var "ipectl") *)
        (* ∗ asn_untrusted *)
        (*     (term_var "segb1") (term_var "segb2") (term_var "pc_old") *)

        ∗ term_var "pc_old" i↦ term_var "id";

      sep_contract_result          := "v";
      sep_contract_postcondition   :=
          MPUIPC0_reg    ↦ term_var "ipectl"
        ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
        ∗ MPUIPSEGB2_reg ↦ term_var "segb2"
        ∗ asn_mpu_registers

        ∗ PC_reg ↦ term_var "pc_old" +' 2

        ∗ term_var "pc_old" i↦ term_var "id"
        ∗ ∃ "w",
          ( term_var "v" = term_union Uwordbyte Kword (term_var "w")

          ∗ ( ∃ "i", ( term_var "id" = term_union Uinstr_or_data Ki (term_var "i")
                     ∗ term_var "w" ≡ term_var "i")
            ∨ term_var "id" = term_union Uinstr_or_data Kd (term_var "w")));

      (* encodes_instr is duplicable *)

        (* ∗ ∃ "pc_new", *)
        (*   ( term_var "pc_new" = term_word_plus [bv 2] (term_var "pc_old") *)
        (*     ∗ PC_reg ↦ term_var "pc_new" *)
        (*     ∗ asn_untrusted *)
        (*         (term_var "segb1") (term_var "segb2") (term_var "pc_new")); *)
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


  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | fetch => Some sep_contract_fetch
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
