From Katamaran Require Import
     Base
     Bitvector
     Iris.Instance
     Iris.Base
     Syntax.Predicates.

Require Import
  Base
  Machine
  IrisModel
  Sig.

From iris.base_logic Require Import invariants lib.iprop lib.gen_heap.
From iris.proofmode Require Import tactics.
From stdpp Require namespaces.
Module ns := stdpp.namespaces.

Set Implicit Arguments.
Import bv.notations.

Module MSP430IrisAdeqParameters <: IrisAdeqParameters MSP430Base MSP430IrisBase.
  (* Pull in the definition of the LanguageMixin and register ghost state. *)
  Import MSP430IrisBase.

  Class mcMemPreGS Σ := {
      mc_ghPreGS :: gen_heapGpreS Address byteBits Σ;
      }.
  #[export] Existing Instance mc_ghPreGS.

  Definition memGpreS : gFunctors -> Set := mcMemPreGS.
  Definition memΣ : gFunctors := #[gen_heapΣ Address byteBits ].

  Lemma NoDup_liveAddrs : NoDup liveAddrs.
  Proof. now eapply Prelude.nodup_fixed. Qed.

  #[global] Arguments liveAddrs : simpl never.

  Definition initMemMap μ := (list_to_map (map (fun a => (a , μ a)) liveAddrs) : gmap Address byteBits).

  Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ.
  Proof. intros. solve_inG. Defined.

  Definition mem_res `{hG : mcMemGS Σ} : Memory -> iProp Σ :=
    fun μ => (([∗ list] a' ∈ liveAddrs, pointsto a' (DfracOwn 1) (μ a')))%I.

  Lemma initMemMap_works μ : map_Forall (λ (a : Address) (v : byteBits), μ a = v) (initMemMap μ).
  Proof.
    unfold initMemMap.
    rewrite map_Forall_to_list.
    rewrite Forall_forall.
    intros (a , v).
    rewrite elem_of_map_to_list.
    intros el.
    apply elem_of_list_to_map_2 in el.
    apply elem_of_list_In in el.
    apply in_map_iff in el.
    by destruct el as (a' & <- & _).
  Qed.

  Lemma big_sepM_list_to_map {Σ} {A B : Type} `{Countable A} {l : list A} {f : A -> B} (F : A -> B -> iProp Σ) :
    NoDup l ->
    ([∗ map] l↦v ∈ (list_to_map (map (λ a : A, (a, f a)) l)), F l v)
      ⊢
      [∗ list] v ∈ l, F v (f v).
  Proof.
    intros ndl.
    induction ndl.
    - now iIntros "_".
    - cbn.
      rewrite big_sepM_insert.
      + iIntros "[$ Hrest]".
        now iApply IHndl.
      + apply not_elem_of_list_to_map_1.
        change (fmap fst ?l) with (map fst l).
        now rewrite map_map map_id.
  Qed.

  Lemma mem_inv_init `{gHP : !mcMemPreGS Σ} (μ : Memory) :
    ⊢ |==> ∃ mG : mcMemGS Σ, (mem_inv mG μ ∗ mem_res μ)%I.
  Proof.
    pose (memmap := initMemMap μ).
    iMod (gen_heap_init (L := Address) (V := byteBits) memmap) as (gH) "[Hinv [Hmapsto _]]".
    iModIntro.
    iExists (McMemGS gH).
    iSplitL "Hinv".
    - iExists memmap.
      iFrame.
      iPureIntro.
      apply initMemMap_works.
    - unfold mem_res, initMemMap in *. iFrame.
      iApply (big_sepM_list_to_map (f := μ) (fun a v => pointsto a (DfracOwn 1) v) with "[$]").
      eapply NoDup_liveAddrs.
  Qed.
End MSP430IrisAdeqParameters.

Module MSP430IrisInstance <:
  IrisInstance MSP430Base MSP430Signature MSP430Program MSP430Semantics
    MSP430IrisBase MSP430IrisAdeqParameters.
  Import MSP430IrisBase.
  Import MSP430Program.

  Section WithSailGS.
    Context `{sailRegGS Σ} `{invGS Σ} `{mG : mcMemGS Σ}.
    (* Variable (live_addrs : list Address). *)

    Definition reg_file : gset (bv 5) := list_to_set (bv.finite.enum 5).

    (* Definition interp_ptsreg (r : registerAddressBits) (v : wordBits) : iProp Σ := *)
    (*   match reg_convert r with *)
    (*   | Some x => reg_pointsTo x v *)
    (*   | None => True *)
    (*   end. *)

    (* Definition interp_gprs : iProp Σ := *)
    (*   [∗ set] r ∈ reg_file, (∃ v, interp_ptsreg r v)%I. *)

    (* Definition PmpEntryCfg : Set := Pmpcfg_ent * Xlenbits. *)

    (* Definition interp_pmp_entries (entries : list PmpEntryCfg) : iProp Σ := *)
    (*   match entries with *)
    (*   | (cfg0, addr0) :: (cfg1, addr1) :: [] => *)
    (*       reg_pointsTo pmp0cfg cfg0 ∗ *)
    (*                    reg_pointsTo pmpaddr0 addr0 ∗ *)
    (*                    reg_pointsTo pmp1cfg cfg1 ∗ *)
    (*                    reg_pointsTo pmpaddr1 addr1 *)
    (*   | _ => False *)
    (*   end. *)

    Definition addr_inc (x : bv 32) (n : nat) : bv 32 :=
      bv.add x (bv.of_nat n).

    Fixpoint get_byte {width : nat} (offset : nat) : bv (width * 8) -> byteBits :=
      match width with
      | O   => fun _ => bv.zero
      | S w =>
          fun bytes =>
            let (byte, bytes) := bv.appView 8 (w * 8) bytes in
            match offset with
            | O        => byte
            | S offset => get_byte offset bytes
            end
      end.

    
    Definition is_mpu_reg_addr (addr : Address) : Prop :=
      bv.ule [bv [16] 0x05A0] addr /\ bv.ult addr [bv 0x05B0].

    Definition interp_ptsto (addr : Address) (b : Byte) : iProp Σ :=
      pointsto addr (DfracOwn 1) b ∗ ⌜¬ is_mpu_reg_addr addr⌝.
    Definition ptstoSth : Address -> iProp Σ := fun a => (∃ w, interp_ptsto a w)%I.
    Definition ptstoSthL : list Address -> iProp Σ :=
      fun addrs => ([∗ list] k↦a ∈ addrs, ptstoSth a)%I.

    Definition interp_ptstomem' {width : nat} (addr : Address) (bytes : bv (width * 8)) : iProp Σ :=
      [∗ list] offset ∈ seq 0 width,
        interp_ptsto (addr + bv.of_nat offset) (get_byte offset bytes).
    Fixpoint interp_ptstomem {width : nat} (addr : Address) : bv (width * 8) -> iProp Σ :=
      match width with
      | O   => fun _ => True
      | S w =>
          fun bytes =>
            let (byte, bytes) := bv.appView 8 (w * 8) bytes in
            interp_ptsto addr byte ∗ interp_ptstomem (bv.one + addr) bytes
      end%I.

    Definition boot_inv_ro_ns : ns.namespace := (ns.ndot ns.nroot "inv_ro").
    Definition interp_ptstomem_readonly {width : nat} (addr : Address) (b : bv (width * 8)) : iProp Σ :=
      inv boot_inv_ro_ns (interp_ptstomem addr b).
    Definition interp_ptsto_readonly (addr : Address) (b : bv 8) : iProp Σ :=
      inv boot_inv_ro_ns (interp_ptsto addr b).

    Definition ptsto_word (addr w : bv 16) :=
      @interp_ptstomem 2 addr w.

    (*
    Definition interp_addr_access_byte (a : Address) : iProp Σ :=
      if decide (a ∈ mmio_addrs) then False%I (* Creates a proof obligation that the adversary cannot access MMIO. TODO: Change this to a trace filter to grant the adversary access to MMIO *)
      else if decide (a ∈ live_addrs) then ptstoSth a
      else True%I. (* Could be `False` as well *)
    Definition interp_addr_access (base : Address) (width : nat): iProp Σ :=
      [∗ list] a ∈ bv.seqBv base width, interp_addr_access_byte a.
     *)

    Definition all_addrs_def : list Address := bv.seqBv bv.zero (Nat.pow 2 16).
    Definition all_addrs_aux : seal (@all_addrs_def). Proof using Type. by eexists. Qed.
    Definition all_addrs : list Address := all_addrs_aux.(unseal).
    Lemma all_addrs_eq : all_addrs = all_addrs_def. Proof using Type. rewrite -all_addrs_aux.(seal_eq) //. Qed.

    Definition untrusted (segb1 segb2 addr : wordBits) : Prop :=
      bv.ult addr (bv.shiftl segb1 [bv [3] 4])
      \/ bv.ule (bv.shiftl segb2 [bv [3] 4]) addr.

    Definition interp_accessible_addresses (segb1 segb2 : wordBits) : iProp Σ :=
      [∗ list] a ∈ all_addrs,
        (⌜untrusted segb1 segb2 a /\ ¬ is_mpu_reg_addr a⌝ -∗ ptstoSth a)%I.

    Definition interp_accessible_addresses_without (segb1 segb2 addr : wordBits) : iProp Σ :=
      (ptstoSth addr -∗ interp_accessible_addresses segb1 segb2)%I.

    Definition interp_ptstoinstr (addr : Address) (id : instr_or_data) : iProp Σ :=
      (∃ v, @interp_ptstomem 2 addr v
              ∗ ⌜ match id with
                  | D v' => v = v'
                  | I i => pure_decode (Word v) = inr i
                  end ⌝)%I.

  End WithSailGS.

  Section MSP430IrisPredicates.

    Import env.notations.

    Equations(noeqns) luser_inst `{sailRegGS Σ, invGS Σ, mcMemGS Σ}
      (p : Predicate) (ts : Env Val (𝑯_Ty p)) : iProp Σ :=
    | accessible_addresses         | [ segb1; segb2 ]       => interp_accessible_addresses segb1 segb2
    | accessible_addresses_without | [ segb1; segb2; addr ] => interp_accessible_addresses_without segb1 segb2 addr
    | instr_arg                    | [ _ ]                  => True
    | encodes_instr                | [ code; instr ]        => ⌜ pure_decode (Word code) = inr instr ⌝%I
    | ptstomem                     | [ addr; b]             => @interp_ptstomem _ _ 1 addr b
    | ptstoinstr                   | [ addr; instr ]        => interp_ptstoinstr addr instr.

    Definition lduplicate_inst `{sailRegGS Σ, invGS Σ, mcMemGS Σ} :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
        is_duplicable p = true ->
        (luser_inst p ts) ⊢ (luser_inst p ts ∗ luser_inst p ts).
    Proof.
      destruct p; intros ts Heq; try discriminate Heq;
        clear Heq; cbn in *; env.destroy ts; cbn; auto.
    Qed.

  End MSP430IrisPredicates.

  Include IrisSignatureRules MSP430Base MSP430Signature MSP430Program
    MSP430Semantics MSP430IrisBase.
  Include IrisAdequacy MSP430Base MSP430Signature MSP430Program
    MSP430Semantics MSP430IrisBase MSP430IrisAdeqParameters.

End MSP430IrisInstance.
