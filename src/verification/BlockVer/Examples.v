From Coq Require Import
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Katamaran Require Import
     Notations
     Bitvector
     Semantics.

From MSP430 Require Import
  BlockVer.Spec
  BlockVer.Verifier
  Machine
  Sig.

Import MSP430Program.
Import MSP430BlockVerifExecutor.
Import Assembly.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.
Import asn.notations.

Module Examples.
  Definition asn_mpu_registers {Σ} : Assertion Σ :=
      ∃ "MPUCTL0_reg"    , MPUCTL0_reg    ↦ term_var "MPUCTL0_reg"
    ∗ ∃ "MPUCTL1_reg"    , MPUCTL1_reg    ↦ term_var "MPUCTL1_reg"
    ∗ ∃ "MPUSEGB2_reg"   , MPUSEGB2_reg   ↦ term_var "MPUSEGB2_reg"
    ∗ ∃ "MPUSEGB1_reg"   , MPUSEGB1_reg   ↦ term_var "MPUSEGB1_reg"
    ∗ ∃ "MPUSAM_reg"     , MPUSAM_reg     ↦ term_var "MPUSAM_reg".

  Definition minimal_pre {Σ} : Assertion Σ :=
    ∃ "ipectl", MPUIPC0_reg    ↦ term_var "ipectl" ∗
    ∃ "segb1" , MPUIPSEGB1_reg ↦ term_var "segb1"  ∗
    ∃ "segb2" , MPUIPSEGB2_reg ↦ term_var "segb2"  ∗
    asn_mpu_registers.

  Definition minimal_post {Σ} : Assertion Σ := minimal_pre.

  Definition VC_triple {Σ}
    (P : Assertion (Σ ▻ "a" :: ty.Address))
    (i : list ast_with_args)
    (Q : Assertion (Σ ▻ "a" :: ty.Address ▻ "an" :: ty.Address))
  :=
    cblock_verification_condition (minimal_pre ∗ P) i (minimal_post ∗ Q).


  Definition Valid_VC {Σ}
    (P : Assertion (Σ ▻ "a" :: ty.Address))
    (i : list ast_with_args)
    (Q : Assertion (Σ ▻ "a" :: ty.Address ▻ "an" :: ty.Address))
  :=
    VC_triple P i Q
    (* safeE (postprocess (VC_triple P i Q)) *).

  (*
  Definition Debug_VC {Σ}
    (P : Assertion (Σ ▻ "a" :: ty.Address))
    (i : list ast_with_args)
    (Q : Assertion (Σ ▻ "a" :: ty.Address ▻ "an" :: ty.Address))
  :=
    VerificationCondition (postprocess (VC_triple P i Q)).
   *)

  Record BlockVerifierContract {Σ} :=
    MkBlockVerifierContract
      { precondition  : Assertion (Σ ▻ "a" :: ty.Address)
      ; instrs        : list ast_with_args
      ; postcondition : Assertion (Σ ▻ "a" :: ty.Address ▻ "an" :: ty.Address)
      }.

  Definition map {Σ A} (c : @BlockVerifierContract Σ)
    (f : Assertion (Σ ▻ "a" :: ty.Address) -> list ast_with_args -> Assertion (Σ ▻ "a" :: ty.Address ▻ "an" :: ty.Address) -> A)
    : A :=
    match c with
    | {| precondition := pre; instrs := i; postcondition := post |} =>
        f pre i post
    end.

  Definition ValidBlockVerifierContract {Σ} (c : @BlockVerifierContract Σ) : Prop :=
    map c Valid_VC.

  Local Notation "'{{' P '}}' i '{{' Q '}}'" :=
    (@MkBlockVerifierContract [ctx] P%asn i Q%asn)
      (at level 90, format "'[v' '{{'  P  '}}' '/'  i '/' '{{'  Q  '}}' ']'").

  Local Ltac solve_bv :=
      repeat match goal with
        | |- context[bv.add ?x (@BitvectorBase.bv.mk ?n 0 I)] =>
            fold (@bv.zero n)
        | |- context[bv.add ?x bv.zero] =>
            rewrite BitvectorBase.bv.add_zero_r
        end.

  Local Ltac solve_vc :=
    vm_compute; constructor; cbn; intros; repeat split; try solve_bv; auto.

  Definition asn_init_pc {Σ} : Assertion (Σ ▻ "a" :: ty.Address) :=
    term_var "a" = term_val ty.Address bv.zero.

  Definition ex_mov_register : BlockVerifierContract :=
    {{
        asn_init_pc ∗
        R4_reg ↦ term_val ty.wordBits [bv 42] ∗
        ∃ "v", R5_reg ↦ term_var "v"
    }}

    [MOV_WRR R4 R5]

    {{
        R4_reg ↦ term_val ty.wordBits [bv 42] ∗
        R5_reg ↦ term_val ty.wordBits [bv 42]
    }}.

  Example valid_ex_move_register : ValidBlockVerifierContract ex_mov_register.
  Proof.
    (* solve_vc. *)
   vm_compute.
vm_compute; constructor; cbn; intros; repeat split; try solve_bv; auto
  Qed.

End Examples.
