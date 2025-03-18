From Coq Require Import
  Lists.List
  Classes.EquivDec
  ZArith.

From Equations Require Import
  Equations.

From Katamaran Require Import
  Notations
  Specification
  Bitvector.

Require Import Base.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
(* Import bv.notations. *)
Import option.notations.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Inductive PurePredicate : Set :=
| mpu_pwd_correct_p
| mpu_pwd_incorrect_p
| ipe_enabled_p
| ipe_locked_p
| ipe_unlocked_p
| access_allowed_p.

Inductive Predicate :=
| ptstomem
| ipe_ctl
| accessible_addresses.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for PurePredicate.
  Derive NoConfusion for Predicate.
End TransparentObligations.

Derive EqDec for PurePredicate.
Derive EqDec for Predicate.

Module Export MSP430Signature <: Signature MSP430Base.
  Import MSP430Base.

  Section PredicateKit.
    Local Definition get_bit {n} (v : bv n) (i : nat) {p : IsTrue (Nat.leb (i + 1) n)}: bool :=
      bv.msb (@bv.vector_subrange n i 1 p v).

    Definition mpu_pwd_correct_inst (ctl : Val (ty.record Ripe_ctl)) := mpu_pwd_correct ctl = true.
    Definition mpu_pwd_incorrect_inst (ctl : Val (ty.record Ripe_ctl)) := mpu_pwd_correct ctl = false.
    Definition ipe_enabled_inst (ctl : Val (ty.record Ripe_ctl)) := ipe_enabled ctl = true.
    Definition ipe_locked_inst (ctl : Val (ty.record Ripe_ctl)) := ipe_locked ctl = true.
    Definition ipe_unlocked_inst (ctl : Val (ty.record Ripe_ctl)) := ipe_locked ctl = false.

    Definition access_allowed_inst
      (ctl  : Val (ty.record Ripe_ctl))
      (am   : Val (ty.enum Eaccess_mode))
      (pc   : Val ty.wordBits)
      (addr : Val ty.Address)
      : Prop
    :=
      let addr := bv.unsigned addr in
      let pc   := bv.unsigned pc in
      let low  := ipe_low_bound ctl in
      let high := ipe_high_bound ctl in

      (* IPE disabled *)
      ipe_enabled ctl = false
      (* address not in IPE segment *)
      \/ (Z.lt addr low \/ Z.le high addr)
      \/ ((* PC in IPE segment except first 8 bytes *)
          Z.le (low + 8) pc /\ Z.lt pc high
          (* not execute access in IVT or RV (9.4.1) *)
          /\ ((Z.lt addr 0xFF80 \/ Z.le 0xFFFF addr)
              \/ am <> X)).

    Definition 𝑷 := PurePredicate.

    (* Maps each pure predicate to a list of arguments with their types. *)
    Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
      match p with
      | mpu_pwd_correct_p | mpu_pwd_incorrect_p | ipe_enabled_p
      | ipe_locked_p | ipe_unlocked_p => [ty.record Ripe_ctl]
      | access_allowed_p => [ty.record Ripe_ctl; ty.enum Eaccess_mode; ty.wordBits; ty.Address]
      end.

    (* Interprets a pure predicate name as a Coq proposition. *)
    Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
      match p with
      | mpu_pwd_correct_p => mpu_pwd_correct_inst
      | mpu_pwd_incorrect_p => mpu_pwd_incorrect_inst
      | ipe_enabled_p => ipe_enabled_inst
      | ipe_locked_p => ipe_locked_inst
      | ipe_unlocked_p => ipe_unlocked_inst
      | access_allowed_p => access_allowed_inst
      end.

    Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

    Definition 𝑯 := Predicate.

    (* 𝑯_Ty defines the signatures of the spatial predicates. *)
    Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
      match p with
      | ptstomem => [ty.Address; ty.byteBits]
      | ipe_ctl => [ty.record Ripe_ctl]
      | accessible_addresses => [ty.record Ripe_ctl]
      end.

    (* 𝑯_is_dup specifies which predicates are duplicable. A spatial predicate can
     be duplicable if it is timeless. Note that spatial predicates are defined
     using the Iris logic, while pure predicates are defined using standard
     Coq. *)
    Global Instance 𝑯_is_dup : IsDuplicable Predicate := {
        is_duplicable p := false
      }.

    Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.

    Local Arguments Some {_} &.

    (* 𝑯_precise specifies which predicates are precise and gives information
     about the input and output parameters of a predicate. *)
    Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
      match p with
      | ipe_ctl => Some (MkPrecise ε [ty.record Ripe_ctl] eq_refl)
      | _ => None
      end.

  End PredicateKit.

  Include PredicateMixin MSP430Base.
  Include WorldsMixin MSP430Base.

  (* In the MSP430SolverKit we provide simplification procedures for the pure
     predicates and prove that these simplifiers are sound. *)
  Section MSP430SolverKit.
    Import Entailment.

    Definition solve_user : SolverUserOnly :=
      fun Σ p ts => Some [formula_user p ts]%ctx.

    Definition solver : Solver := solveruseronly_to_solver solve_user.

    Lemma solve_user_spec : SolverUserOnlySpec solve_user.
    Proof.
      intros Σ p ts.
      destruct p; cbv in ts; env.destroy ts; reflexivity.
    Qed.

    Lemma solver_spec : SolverSpec solver.
    Proof.
      apply solveruseronly_to_solver_spec, solve_user_spec.
    Qed.
  End MSP430SolverKit.

  Include SignatureMixin MSP430Base.
End MSP430Signature.
