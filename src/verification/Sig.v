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
| untrusted.

Inductive Predicate :=
| ptstomem
| ptstoinstr
| encodes_instr
| accessible_addresses
| accessible_addresses_without.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for PurePredicate.
  Derive NoConfusion for Predicate.
End TransparentObligations.

Derive EqDec for PurePredicate.
Derive EqDec for Predicate.

Definition puntrusted (segb1 segb2 pc : bv 16) : Prop :=
  bv.unsigned pc < bv.unsigned segb1 * 16 \/
  bv.unsigned segb2 * 16 <= bv.unsigned pc.

Module Export MSP430Signature <: Signature MSP430Base.
  Import MSP430Base.

  Section PredicateKit.

    Definition 𝑷 := PurePredicate.

    (* Maps each pure predicate to a list of arguments with their types. *)
    Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
      match p with
      | untrusted => [ty.Address; ty.Address; ty.Address]
      end.

    (* Interprets a pure predicate name as a Coq proposition. *)
    Definition 𝑷_inst (p : 𝑷) : env.abstract Val (𝑷_Ty p) Prop :=
      match p with
      | untrusted => puntrusted
      end.

    Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

    Definition 𝑯 := Predicate.

    (* 𝑯_Ty defines the signatures of the spatial predicates. *)
    Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
      match p with
      | ptstomem => [ty.Address; ty.byteBits]
      | ptstoinstr => [ty.Address; ty.union Uinstr_or_data]
      | encodes_instr => [ty.wordBits; ty.union Uast]
      | accessible_addresses => [ty.wordBits; ty.wordBits]
      | accessible_addresses_without => [ty.wordBits; ty.wordBits; ty.Address]
      end.

    (* 𝑯_is_dup specifies which predicates are duplicable. A spatial predicate can
     be duplicable if it is timeless. Note that spatial predicates are defined
     using the Iris logic, while pure predicates are defined using standard
     Coq. *)
    Global Instance 𝑯_is_dup : IsDuplicable Predicate := {
        is_duplicable p := match p with encodes_instr => true | _ => false end
      }.

    Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.

    Local Arguments Some {_} &.

    (* 𝑯_precise specifies which predicates are precise and gives information
     about the input and output parameters of a predicate. *)
    Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
      match p with
      | ptstomem => Some (MkPrecise [ty.Address] [ty.byteBits] eq_refl)
      | ptstoinstr => Some (MkPrecise [ty.Address] [ty.union Uinstr_or_data] eq_refl)
      | encodes_instr => Some (MkPrecise [ty.wordBits] [ty.union Uast] eq_refl)
      | accessible_addresses => Some (MkPrecise [ty.wordBits; ty.wordBits] ε eq_refl)
      | accessible_addresses_without => Some (MkPrecise [ty.wordBits; ty.wordBits; ty.Address] ε eq_refl)
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

