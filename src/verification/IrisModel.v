From Katamaran Require Import
     Bitvector
     Environment
     Iris.Base
     trace.
From iris Require Import
     base_logic.lib.gen_heap
     proofmode.tactics.
Require Import Machine.

Set Implicit Arguments.

Import MSP430Program.

(* Instantiate the Iris framework solely using the operational semantics. At
   this point we do not commit to a set of contracts nor to a set of
   user-defined predicates. *)
Module MSP430IrisBase <: IrisBase MSP430Base MSP430Program MSP430Semantics.
  (* Pull in the definition of the LanguageMixin and register ghost state. *)
  Include IrisPrelims MSP430Base MSP430Program MSP430Semantics.

  (* Defines the memory ghost state. *)
  Section MSP430IrisParams.
    Import bv.
    Definition Byte : Set := bv 8.
    Definition MemVal : Set := Byte.

    (* NOTE: no resource present for current `State`, since we do not wish to reason about it for now *)
    Class mcMemGS Σ :=
      McMemGS {
          (* ghost variable for tracking state of heap *)
          mc_ghGS : gen_heapGS Address byteBits Σ;
          (* tracking traces *)
          (* mc_gtGS : traceG Trace Σ; *)
        }.
    #[export] Existing Instance mc_ghGS.
    (* #[export] Existing Instance mc_gtGS. *)

    Definition memGS : gFunctors -> Set := mcMemGS.

    Definition mem_inv : forall {Σ}, mcMemGS Σ -> Memory -> iProp Σ :=
      fun {Σ} hG μ =>
        (∃ memmap, gen_heap_interp memmap
           ∗ ⌜ map_Forall (fun a v => μ a = v) memmap ⌝
           (* ∗ tr_auth1 (memory_trace μ) *)
        )%I.

  End MSP430IrisParams.

  Include IrisResources MSP430Base MSP430Program MSP430Semantics.
  Include IrisWeakestPre MSP430Base MSP430Program MSP430Semantics.
  Include IrisTotalWeakestPre MSP430Base MSP430Program MSP430Semantics.
  Include IrisTotalPartialWeakestPre MSP430Base MSP430Program MSP430Semantics.

  Import iris.program_logic.weakestpre.

  Definition WP_loop `{sg : sailGS Σ} : iProp Σ :=
    semWP env.nil (FunDef loop) (fun _ _ => True%I).

  (* Useful instance for some of the Iris proofs *)
  #[export] Instance state_inhabited : Inhabited State.
  Proof. repeat constructor.
          - intros ty reg. apply val_inhabited.
          - intro. apply bv.bv_inhabited.
          (* - apply state_inhabited. *)
  Qed.

End MSP430IrisBase.
