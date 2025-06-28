From Coq Require Import
     Lists.List.
From Katamaran Require Import
     Bitvector
     Environment
     Iris.Instance
     Iris.Base
     Program
     Semantics
     Sep.Hoare
     Specification
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.RefineExecutor
     MicroSail.Soundness.

Require Import
     Machine
     Sig
     IrisModel
     IrisInstance
     Model
     Contracts.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import string_ident tactics.

Set Implicit Arguments.
Import ListNotations.
Import MSP430Specification.
Import MSP430Program.
Import MSP430IrisBase.
Import MSP430IrisInstance.
Import MSP430Model.
(* Import MSP430ValidContracts. *)

Import MSP430Signature.
Module Import MSP430ShallowExecutor :=
  MakeShallowExecutor MSP430Base MSP430Signature MSP430Program MSP430Specification.

Module Import MSP430ShallowSoundness := MakeShallowSoundness MSP430Base MSP430Signature MSP430Program MSP430Specification MSP430ShallowExecutor MSP430ProgramLogic.

Module Import MSP430Symbolic := MakeSymbolicSoundness MSP430Base MSP430Signature MSP430Program MSP430Specification MSP430ShallowExecutor MSP430Executor.

Section Loop.
  Context `{sg : sailGS Σ}.

  Local Notation "r '↦' val" := (reg_pointsTo r val) (at level 70).
  Local Opaque liveAddrs.

  Import bv.notations.
  Compute bv.eqb (bv.drop 6 [bv [16] 0xC0]) [bv 0x3].

  Definition own_registers : iProp Σ :=
      (∃ v, SP_reg ↦ v)
    ∗ (∃ v, SRCG1_reg ↦ v)
    ∗ (∃ v, CG2_reg ↦ v)
    ∗ (∃ v, R4_reg ↦ v)
    ∗ (∃ v, R5_reg ↦ v)
    ∗ (∃ v, R6_reg ↦ v)
    ∗ (∃ v, R7_reg ↦ v)
    ∗ (∃ v, R8_reg ↦ v)
    ∗ (∃ v, R9_reg ↦ v)
    ∗ (∃ v, R10_reg ↦ v)
    ∗ (∃ v, R11_reg ↦ v)
    ∗ (∃ v, R12_reg ↦ v)
    ∗ (∃ v, R13_reg ↦ v)
    ∗ (∃ v, R14_reg ↦ v)
    ∗ (∃ v, R15_reg ↦ v)
    ∗ (∃ v, MPUCTL0_reg ↦ v)
    ∗ (∃ v, MPUCTL1_reg ↦ v)
    ∗ (∃ v, MPUSEGB2_reg ↦ v)
    ∗ (∃ v, MPUSEGB1_reg ↦ v)
    ∗ (∃ v, MPUSAM_reg ↦ v)
    ∗ (∃ v, LastInstructionFetch ↦ v).

  Definition loop_pre (pc ipectl segb1 segb2 : bv 16) : iProp Σ :=
      PC_reg         ↦ pc
    ∗ MPUIPC0_reg    ↦ ipectl
    ∗ MPUIPSEGB1_reg ↦ segb1
    ∗ MPUIPSEGB2_reg ↦ segb2

    (* ipe configured *)
    ∗ ⌜bv.drop 6 ipectl = [bv 0x3]⌝
    ∗ ⌜bv.ult segb1 segb2⌝

    (* pc untrusted *)
    ∗ (⌜(bv.unsigned pc < bv.unsigned segb1 * 16)%Z⌝
       ∨ ⌜(bv.unsigned segb2 * 16 <= bv.unsigned pc)%Z⌝)

    ∗ interp_accessible_addresses segb1 segb2

    ∗ own_registers

    (* TODO add other registers, memory etc. to the lhs *)
    ∗ ▷ (PC_reg ↦ segb1 + [bv 8] -∗ WP_loop).

  Definition semTriple_loop : iProp Σ :=
    (∀ pc ipectl segb1 segb2,
        semTriple env.nil
          (loop_pre pc ipectl segb1 segb2)
          (FunDef loop)
          (fun _ _ => True))%I.

  Lemma valid_semTriple_loop : ⊢ semTriple_loop.
  Admitted.
End Loop.
