From Coq Require Import
  Lists.List
  Strings.String
  ZArith.

From Katamaran Require Import
     Notations
     Specification
     Assertions.

Require Import
  Machine
  Sig.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
(* Import bv.notations. *)
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

    Local Notation asn_access_allowed addr am pc MPUIPC0 MPUIPSEGB1 MPUIPSEGB2:=
      (asn.formula (formula_user access_allowed
                      [addr; term_enum Eaccess_mode am; term_var pc;
                       term_var MPUIPC0; term_var MPUIPSEGB1; term_var MPUIPSEGB2])).

    (* Foreign function contracts *)

    Definition sep_contract_undefined_bitvector (n : nat) :
      SepContractFunX (@undefined_bitvector n) :=
      {|
        sep_contract_logic_variables := ["_" :: ty.int];
        sep_contract_localstore      := [term_var "_"];
        sep_contract_precondition    := ⊤;
        sep_contract_result          := "v";
        sep_contract_postcondition   := ∃ "w", term_var "v" = term_var "w";
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
        sep_contract_result          := "_";
        sep_contract_postcondition   := term_var "addr" m↦ term_var "v";
      |}.

    (* μSail function contracts *)

    Definition sep_contract_read_mem_aux :
      SepContractFun read_mem_aux :=
      {|
        sep_contract_logic_variables :=
          ["bw" :: ty.enum Ebw; "addr" :: ty.Address; "m" :: ty.enum Eaccess_mode;
           "MPUCTL0" :: ty.wordBits; "MPUIPSEGB1" :: ty.wordBits; "MPUIPSEGB2" :: ty.wordBits;
           "pc" :: ty.wordBits; "vl" :: ty.byteBits; "vh" :: ty.byteBits];

        sep_contract_localstore := [term_var "bw"; term_var "addr"; term_var "m"];

        sep_contract_precondition :=
            term_var "addr" m↦ term_var "vl"
          ∗ PC_reg ↦ term_var "pc"
          ∗ MPUCTL0_reg ↦ term_var "MPUCTL0"
          ∗ MPUIPSEGB1_reg ↦ term_var "MPUIPSEGB1"
          ∗ MPUIPSEGB2_reg ↦ term_var "MPUIPSEGB2"
          ∗ asn_access_allowed (term_var "addr") R "pc" "MPUCTL0" "MPUIPSEGB1" "MPUIPSEGB2"
          ∗ match_bw (term_var "bw")
              ⊤
              (inc "addr" m↦ term_var "vh"
               ∗ asn_access_allowed (inc "addr") R "pc" "MPUCTL0" "MPUIPSEGB1" "MPUIPSEGB2");

        sep_contract_result          := "w";
        sep_contract_postcondition   :=
            term_var "addr" m↦ term_var "vl"
          ∗ match_bw (term_var "bw")
              (term_var "w" = term_union Uwordbyte Kbyte (term_var "vl"))
              (inc "addr" m↦ term_var "vh"
               ∗ term_var "w" = term_union Uwordbyte Kword (term_var "vh" ++ term_var "vl"));
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
