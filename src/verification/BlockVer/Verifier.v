From Coq Require Import
     Classes.Morphisms_Prop
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Equations Require Import
     Equations.
From Katamaran Require Import
     Iris.Instance
     Iris.Base
     Notations
     Semantics
     Bitvector
     Refinement.Monads
     Sep.Hoare
     Specification
     Symbolic.Propositions
     Symbolic.Solver
     Symbolic.Worlds
     MicroSail.ShallowExecutor
     MicroSail.ShallowSoundness
     MicroSail.SymbolicExecutor
     MicroSail.RefineExecutor
     MicroSail.Soundness.
From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.
From stdpp Require namespaces.

From MSP430 Require Import Machine Sig BlockVer.Spec.

Import MSP430Program.
Import Assembly.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import bv.notations.
Import ListNotations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Section BlockVerificationDerived.

  Import MSP430BlockVerifExecutor.
  Import MSP430BlockVerifShalExecutor.

  (*
  Definition safeE {Σ} : 𝕊 Σ -> Prop :=
    fun P => VerificationConditionWithErasure (Erasure.erase_symprop P).

  Definition safeE_safe (p : 𝕊 wnil) (ι : Valuation wnil) : safeE p -> SymProp.safe p [].
  Proof.
    unfold safeE.
    destruct 1 as [H].
    now apply Erasure.erase_safe'.
  Qed.
  *)

  Local Notation "r m↦ v" := (asn.chunk (chunk_user ptstomem [r; v])) (at level 70).
  Local Notation "r i↦ v" := (asn.chunk (chunk_user ptstoinstr [r; v])) (at level 70).

  Local Notation "v +' n" :=  (term_binop bop.bvadd v (term_val ty.wordBits [bv n])) (at level 50).

  Definition instr_size (i : ast) : bv 16  :=
    let aux : AM -> bv 16 :=
      fun am =>
        match am with
        | REGISTER_MODE
        | INDIRECT_REGISTER_MODE
        | INDIRECT_AUTOINCREMENT_MODE => [bv 0]
        | INDEXED_MODE => [bv 2]
        end%N
    in
    bv.add
      (match i with
       | DOUBLEOP _ _ _ am1 _ am2 => bv.add (aux am1) (aux am2)
       | SINGLEOP _ _ am _ => aux am
       | JUMP _ _ | DOESNOTUNDERSTAND _ => [bv 0]
       end) [bv 2].

  Section Symbolic.

    Import ModalNotations.
    Import SStoreSpec (evalStoreSpec).
    Import SHeapSpec SHeapSpec.notations.
    Import asn.notations.


    Definition ptstoinstr_with_args {Σ} addr (i : ast_with_args) : Assertion Σ :=
      addr i↦ term_val (ty.union Uinstr_or_data) (I (instr_without_args i))
      ∗ match i with
        | I0 _     => ⊤
        | I1 _ a   => addr +' 2 i↦ term_val (ty.union Uinstr_or_data) (D a)
        | I2 _ a b =>
              addr +' 2 i↦ term_val (ty.union Uinstr_or_data) (D a)
            ∗ addr +' 4 i↦ term_val (ty.union Uinstr_or_data) (D b)
        end.

    Definition exec_instruction_prologue (i : ast_with_args) :
      Assertion ([ctx] ▻ ("a":: ty.Address))
    :=
        PC_reg ↦ term_var "a"
      ∗ ptstoinstr_with_args (term_var "a") i.

    (* ∃ "an", nextpc ↦ term_var "an" *) (* TODO what is nextpc? *)

    Definition exec_instruction_epilogue (i : ast_with_args) :
      Assertion ([ctx] ▻ ("a":: ty.Address) ▻ ("na":: ty.Address))
    :=
        PC_reg ↦ term_var "na"
      ∗ ptstoinstr_with_args (term_var "a") i.
  
      (* ∗ nextpc ↦ term_var "na" *)

  End Symbolic.

  Section Shallow.

    Import CStoreSpec (evalStoreSpec).
    Import CHeapSpec CHeapSpec.notations.

    Definition cexec_instruction (i : ast_with_args) :
      Val ty.Address -> CHeapSpec (Val ty.Address) :=
      let inline_fuel := 10%nat in
      fun a =>
        _ <- produce (exec_instruction_prologue i)
               [env].["a"∷_ ↦ a] ;;
        w <- evalStoreSpec (cexec inline_fuel (FunDef fetch))
               [env].["_ж716"∷_ ↦ tt] ;;
        d <- cexec_call_foreign decode
               [env].["w"∷_ ↦ w] ;;
        _ <- evalStoreSpec (cexec inline_fuel (FunDef execute))
               [env].["merge#var"∷_ ↦ d] ;;
        na <- angelic _ ;;
        _ <- consume
               (exec_instruction_epilogue i)
               [env].["a"∷ty.Address ↦ a].["na"∷_ ↦ na] ;;
        pure na.

    Fixpoint cexec_block_addr (b : list ast_with_args) :
      Val ty.Address -> Val ty.Address -> CHeapSpec (Val ty.Address) :=
      fun ainstr apc =>
        match b with
        | nil       => pure apc
        | cons i b' =>
            _ <- assert_formula (ainstr = apc) ;;
            apc' <- cexec_instruction i apc ;;
            cexec_block_addr b'
              (bv.add ainstr (instr_size (instr_without_args i)))
              apc'
        end.

    Definition cexec_double_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty.Address)) (b : list ast_with_args) :
      CHeapSpec (Val ty.Address) :=
      δ <- demonic_ctx Σ ;;
      an <- demonic _ ;;
      _ <- produce req δ.["a"∷ty.Address ↦ an] ;;
      cexec_block_addr b an an.

    Definition cexec_triple_addr {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty.Address)) (b : list ast_with_args)
      (ens : Assertion (Σ ▻ "a"∷ty.Address ▻ "an"∷ty.Address)) :
      CHeapSpec unit :=
      lenv <- demonic_ctx Σ ;;
      a    <- demonic _ ;;
      _    <- produce req lenv.["a"∷ty.Address ↦ a]  ;;
      na   <- cexec_block_addr b a a ;;
      consume ens lenv.["a"∷ty.Address ↦ a].["an"∷ty.Address ↦ na].

    Definition cblock_verification_condition {Σ : LCtx}
      (req : Assertion (Σ ▻ "a"∷ty.Address)) (b : list ast_with_args)
      (ens : Assertion (Σ ▻ "a"∷ty.Address ▻ "an"∷ty.Address)) : Prop
    := CHeapSpec.run (cexec_triple_addr req b ens).

    Import (hints) CStoreSpec.

    #[export] Instance mono_cexec_instruction {i a} :
      Monotonic (MHeapSpec eq) (cexec_instruction i a).
    Proof. typeclasses eauto. Qed.

    #[export] Instance mono_cexec_block_addr {instrs ainstr apc} :
      Monotonic (MHeapSpec eq) (cexec_block_addr instrs ainstr apc).
    Proof. revert ainstr apc. induction instrs; cbn; typeclasses eauto. Qed.
  End Shallow.
End BlockVerificationDerived.
