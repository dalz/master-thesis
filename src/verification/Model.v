From Coq Require Import
     Program.Tactics
     Lists.List.
From Katamaran Require Import
     Bitvector
     Environment
     Iris.Instance
     Iris.Base
     Program
     Semantics
     Sep.Hoare
     Specification.

Require Import
     Machine
     Contracts
     IrisModel
     IrisInstance
     Sig.

From Equations Require Import
     Equations.

From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require Import weakestpre total_weakestpre adequacy.
From iris.program_logic Require lifting.
From iris.program_logic Require total_lifting.
From iris.proofmode Require Import string_ident tactics.

Set Implicit Arguments.
Import ListNotations.
Import bv.notations.

Import MSP430Program.
Import MSP430Signature.

Import MSP430IrisBase.
Import MSP430IrisInstance.

Module MSP430Model.
  Import MSP430Signature.
  Import MSP430Specification.
  Import MSP430Program.

  Module MSP430ProgramLogic <: ProgramLogicOn MSP430Base MSP430Signature MSP430Program MSP430Specification.
    Include ProgramLogicOn MSP430Base MSP430Signature MSP430Program MSP430Specification.
  End MSP430ProgramLogic.
  Include MSP430ProgramLogic.

  Include IrisInstanceWithContracts MSP430Base MSP430Signature
    MSP430Program MSP430Semantics MSP430Specification MSP430IrisBase
    MSP430IrisAdeqParameters MSP430IrisInstance.

  (* proofs of lemmas and foreign functions... *)
End MSP430Model.
