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

    Local Notation asn_mpu_pwd_correct mpuctl0 := (asn.formula (formula_user mpu_pwd_correct_p [term_var mpuctl0])).
    Local Notation asn_ipe_enabled ipectl := (asn.formula (formula_user ipe_enabled_p [term_var ipectl])).
    Local Notation asn_ipe_locked ipectl := (asn.formula (formula_user ipe_locked_p [term_var ipectl])).
    Local Notation asn_ipe_unlocked ipectl := (asn.formula (formula_user ipe_unlocked_p [term_var ipectl])).

    Local Notation asn_access_allowed ipectl segb1 segb2 am pc addr :=
      (asn.formula
         (formula_user access_allowed_p
            [ term_var ipectl; term_var segb1; term_var segb2
            ; term_enum Eaccess_mode am; term_var pc; addr])).

    Local Notation asn_ipe_entry_point segb1 addr :=
      (asn.formula (formula_user ipe_entry_point_p [term_var segb1; term_var addr])).

    Local Notation asn_in_ipe_segment segb1 segb2 addr :=
      (asn.formula (formula_user in_ipe_segment_p [term_var segb1; term_var segb2; addr])).
    Local Notation asn_not_in_ipe_segment segb1 segb2 addr :=
      (asn.formula (formula_user not_in_ipe_segment_p [term_var segb1; term_var segb2; addr])).

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

    Definition sep_contract_check_ipe_access :
      SepContractFun check_ipe_access :=
      {|
        sep_contract_logic_variables :=
          [ "addr"     :: ty.Address
          ; "m"        :: ty.enum Eaccess_mode
          ; "ipectl"   :: ty.wordBits
          ; "segb1" :: ty.wordBits
          ; "segb2" :: ty.wordBits
          ; "pc"       :: ty.wordBits          ];

        sep_contract_localstore := [term_var "addr"; term_var "m"];

        sep_contract_precondition :=
            PC_reg         ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"
          ∗ asn_access_allowed "ipectl" "segb1" "segb2" R "pc" (term_var "addr");

        sep_contract_result        := "v";
        sep_contract_postcondition := ⊤ (* term_var "v" = term_val ty.bool true  XXX *);
      |}.

    Definition sep_contract_read_mem_aux :
      SepContractFun read_mem_aux :=
      {|
        sep_contract_logic_variables :=
          ["bw" :: ty.enum Ebw; "addr" :: ty.Address; "m" :: ty.enum Eaccess_mode;
           "ipectl"   :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits;
           "pc" :: ty.wordBits; "vl" :: ty.byteBits; "vh" :: ty.byteBits];

        sep_contract_localstore := [term_var "bw"; term_var "addr"; term_var "m"];

        sep_contract_precondition :=
          term_var "m" = term_enum Eaccess_mode R ∗ (* XXX *)
            term_var "addr" m↦ term_var "vl"
          ∗ PC_reg ↦ term_var "pc"
          ∗ MPUIPC0_reg    ↦ term_var "ipectl"
          ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
          ∗ MPUIPSEGB2_reg ↦ term_var "segb2"
          ∗ asn_access_allowed "ipectl" "segb1" "segb2" R "pc" (term_var "addr")
          ∗ match_bw (term_var "bw")
              ⊤
              (inc "addr" m↦ term_var "vh"
               ∗ asn_access_allowed "ipectl" "segb1" "segb2" R "pc" (inc "addr"));

        sep_contract_result          := "w";
        sep_contract_postcondition   := ⊤;
          (*   term_var "addr" m↦ term_var "vl" *)
          (* ∗ PC_reg ↦ term_var "pc" *)
          (* ∗ asn_ipe_ctl "ipe_ctl" *)
          (* ∗ match_bw (term_var "bw") *)
          (*     (term_var "w" = term_union Uwordbyte Kbyte (term_var "vl")) *)
          (*     (inc "addr" m↦ term_var "vh" *)
          (*      ∗ term_var "w" = term_union Uwordbyte Kword (term_var "vh" ++ term_var "vl")); *)
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
            ∗ (   asn_mpu_pwd_correct "mpuctl0"
                ∗ asn_ipe_unlocked "ipectl"

              ∨ (* otherwise they must stay the same *)
                  term_var "ipectl_new" = term_var "ipectl"
                ∗ term_var "segb1_new"  = term_var "segb1"
                ∗ term_var "segb2_new"  = term_var "segb2"
              )

            ∗ PC_reg ↦ term_var "pc_new"

            ∗ (* jumps to untrusted sections are always allowed *)
              ( asn_not_in_ipe_segment "segb1" "segb2" (term_var "pc_new")

                (* arbitrary jumps into the IPE segment are allowed only from the IPE segment *)
              ∨ asn_access_allowed "ipectl_new" "segb1_new" "segb2_new" X "pc" (term_var "pc_new")

                (* untrusted code can only jump to the entry point *)
              ∨ asn_ipe_entry_point "segb1_new" "pc_new"
              )

            ∗ asn_accessible_addresses "pc_new" "ipectl" "segb1_new" "segb2_new");
      |}.

    (* The following maps μSail function names to their contracts. *)
    Definition CEnv : SepContractEnv :=
      fun Δ τ f =>
        match f with
          | read_mem_aux => Some sep_contract_read_mem_aux
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
        end.
  End ContractDefKit.
End MSP430Specification.

(*** VERIFICATION ***)

Import MSP430Specification.
Import Erasure.notations.

Module MSP430Executor :=
  MakeExecutor MSP430Base MSP430Signature MSP430Program MSP430Specification.

Import MSP430Executor.
Import MSP430Executor.Symbolic.

Ltac symbolic_simpl :=
  apply validcontract_reflect_sound;
  compute;
  constructor;
  cbn.

Ltac symbolic_simpl_with_fuel :=
  apply validcontract_reflect_fuel_sound;
  compute;
  constructor;
  cbn.

Ltac symbolic_simpl_with_erasure :=
  apply validcontract_with_erasure_sound;
  compute;
  constructor;
  cbn.

Lemma valid_contract_check_ipe_access : Symbolic.ValidContractWithFuel 2 sep_contract_check_ipe_access fun_check_ipe_access.
Proof. symbolic_simpl_with_fuel. Qed.

Lemma valid_contract_read_mem_aux : Symbolic.ValidContract sep_contract_read_mem_aux fun_read_mem_aux.
Proof.
  symbolic_simpl.
  intros bw v _ ctl w _ _ Haccess.
  split.
  - intro.
    unfold access_allowed_inst.
    .

Lemma valid_contract_execute : Symbolic.ValidContractReflect sep_contract_execute fun_execute.
Proof. reflexivity. Qed.
