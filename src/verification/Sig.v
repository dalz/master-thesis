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
| ipe_enabled_p
| ipe_locked_p
| ipe_unlocked_p
| access_allowed_p
| in_ipe_segment_p
| not_in_ipe_segment_p
| ipe_entry_point_p.

Inductive Predicate :=
| ptstomem
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

    (*
    Definition mpu_pwd_correct_inst (ctl : Val (ty.record Ripe_ctl)) := mpu_pwd_correct ctl = true.
    Definition mpu_pwd_incorrect_inst (ctl : Val (ty.record Ripe_ctl)) := mpu_pwd_correct ctl = false.
    Definition ipe_enabled_inst (ctl : Val (ty.record Ripe_ctl)) := ipe_enabled ctl = true.
    Definition ipe_locked_inst (ctl : Val (ty.record Ripe_ctl)) := ipe_locked ctl = true.
    Definition ipe_unlocked_inst (ctl : Val (ty.record Ripe_ctl)) := ipe_locked ctl = false.
    *)

    Definition mpu_pwd_correct_inst (mpuctl0 : Val ty.wordBits) : Prop :=
      bv.eqb (bv.vector_subrange 8 8 mpuctl0) (bv.of_Z 0x96) = true.

    Definition ipe_enabled_inst (ipectl : Val ty.wordBits) : Prop :=
      bv.eqb (bv.vector_subrange 6 1 ipectl) (bv.of_Z 1) = true.

    Definition ipe_locked_inst (ipectl : Val ty.wordBits) :=
      bv.eqb (bv.vector_subrange 7 1 ipectl) (bv.of_Z 1) = true.

    Definition ipe_unlocked_inst (ipectl : Val ty.wordBits) :=
      bv.eqb (bv.vector_subrange 7 1 ipectl) (bv.of_Z 1) = true.

    Definition access_allowed_inst
      (ipectl   : Val ty.wordBits)
      (ipesegb1 : Val ty.wordBits)
      (ipesegb2 : Val ty.wordBits)
      (am       : Val (ty.enum Eaccess_mode))
      (pc       : Val ty.wordBits)
      (addr     : Val ty.Address)
      : Prop
    :=
      let addr := bv.unsigned addr in
      let pc   := bv.unsigned pc in
      let low  := bv.unsigned ipesegb1 * 16 in
      let high := bv.unsigned ipesegb2 * 16 in

      (* IPE disabled *)
      ipe_enabled_inst ipectl
      (* address not in IPE segment *)
      \/ (Z.lt addr low \/ Z.le high addr)
      \/ ((* PC in IPE segment except first 8 bytes *)
          Z.le (low + 8) pc /\ Z.lt pc high
          (* not execute access in IVT or RV (9.4.1) *)
          /\ ((Z.lt addr 0xFF80 \/ Z.le 0xFFFF addr)
              \/ am <> X)).

    Definition in_ipe_segment_inst (segb1 segb2 addr : Val ty.wordBits) :=
      bv.unsigned segb1 * 16 <= bv.unsigned addr /\ bv.unsigned addr < bv.unsigned segb2 * 16.

    Definition not_in_ipe_segment_inst (segb1 segb2 addr : Val ty.wordBits) :=
      bv.unsigned segb1 * 16 > bv.unsigned addr \/ bv.unsigned addr >= bv.unsigned segb2 * 16.

    Definition ipe_entry_point_inst (segb1 addr : Val ty.wordBits) :=
      bv.unsigned segb1 * 16 + 8 = bv.unsigned addr.

    Definition 𝑷 := PurePredicate.

    (* Maps each pure predicate to a list of arguments with their types. *)
    Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
      match p with
      | mpu_pwd_correct_p | ipe_enabled_p | ipe_locked_p | ipe_unlocked_p => [ty.wordBits]
      | in_ipe_segment_p | not_in_ipe_segment_p => [ty.wordBits; ty.wordBits; ty.Address]
      | ipe_entry_point_p => [ty.wordBits; ty.Address]
      | access_allowed_p => [ty.wordBits; ty.wordBits; ty.wordBits; ty.enum Eaccess_mode; ty.wordBits; ty.Address]
      end.

    (* Interprets a pure predicate name as a Coq proposition. *)
    Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
      match p with
      | mpu_pwd_correct_p    => mpu_pwd_correct_inst
      | ipe_enabled_p        => ipe_enabled_inst
      | ipe_locked_p         => ipe_locked_inst
      | ipe_unlocked_p       => ipe_unlocked_inst
      | access_allowed_p     => access_allowed_inst
      | in_ipe_segment_p     => in_ipe_segment_inst
      | not_in_ipe_segment_p => not_in_ipe_segment_inst
      | ipe_entry_point_p    => ipe_entry_point_inst
      end.

    Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

    Definition 𝑯 := Predicate.

    (* 𝑯_Ty defines the signatures of the spatial predicates. *)
    Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
      match p with
      | ptstomem => [ty.Address; ty.byteBits]
      | accessible_addresses => [ty.wordBits; ty.wordBits; ty.wordBits; ty.wordBits]
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
      | ptstomem => Some (MkPrecise [ty.Address] [ty.byteBits] eq_refl)
      | accessible_addresses => Some (MkPrecise [ty.wordBits; ty.wordBits; ty.wordBits; ty.wordBits] ε eq_refl)
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

