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
| access_allowed.

Inductive Predicate :=
| ptstomem.

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

    (* Definition ipe_enabled (MPUIPC0 : Val (ty.wordBits)) : Prop :=
      get_bit MPUIPC0 6 = true.

    Definition in_ipe_segment
      (addr          : Val ty.Address)
      (MPUIPSEGB1    : Val ty.wordBits)
      (MPUIPSEGB2    : Val ty.wordBits)
      (low_bound_off : Z)
      : Prop
    :=
      let addr := bv.unsigned addr in
      let low  := (bv.unsigned MPUIPSEGB1 * 16)%Z + low_bound_off in
      let high := (bv.unsigned MPUIPSEGB2 * 16)%Z in
      Z.le low addr /\ Z.lt addr high. *)

    Definition access_allowed_inst
      (addr       : Val ty.Address)
      (am         : Val (ty.enum Eaccess_mode))
      (pc         : Val ty.wordBits)
      (MPUIPC0    : Val ty.wordBits)
      (MPUIPSEGB1 : Val ty.wordBits)
      (MPUIPSEGB2 : Val ty.wordBits)
      : Prop
    :=
      let addr := bv.unsigned addr in
      let pc   := bv.unsigned pc in
      let low  := (bv.unsigned MPUIPSEGB1 * 16)%Z in
      let high := (bv.unsigned MPUIPSEGB2 * 16)%Z in

    (* IPE disabled *)
    get_bit MPUIPC0 6 = false
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
      | access_allowed => [ty.Address; ty.enum Eaccess_mode; ty.wordBits; ty.wordBits; ty.wordBits; ty.wordBits]
      end.

    (* Interprets a pure predicate name as a Coq proposition. *)
    Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
      match p with
      | access_allowed => access_allowed_inst
      end.

    Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

    Definition 𝑯 := Predicate.

    (* 𝑯_Ty defines the signatures of the spatial predicates. *)
    Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
      match p with
      | ptstomem => [ty.Address; ty.byteBits]
      end.

    (* 𝑯_is_dup specifies which predicates are duplicable. A spatial predicate can
     be duplicable if it is timeless. Note that spatial predicates are defined
     using the Iris logic, while pure predicates are defined using standard
     Coq. *)
    Global Instance 𝑯_is_dup : IsDuplicable Predicate := {
        is_duplicable p := false
      }.

    Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.

    (* 𝑯_precise specifies which predicates are precise and gives information
     about the input and output parameters of a predicate. *)
    Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) := None.

  End PredicateKit.

  Include PredicateMixin MSP430Base.
  Include WorldsMixin MSP430Base.

  (* In the MinCapsSolverKit we provide simplification procedures for the pure
     predicates and prove that these simplifiers are sound. *)
  Section MSP430SolverKit.
    Definition solver : Solver := fun _ _ => None.

    Lemma solver_spec : SolverSpec solver.
    Proof.
    Admitted.
  End MSP430SolverKit.

  Include SignatureMixin MSP430Base.
End MSP430Signature.
