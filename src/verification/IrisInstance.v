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

  (* this is in Base.v in the RiscvPmp case study *)
  Definition minAddr : nat := 0.
  Definition lenAddr : nat := 200.
  Definition maxAddr : nat := minAddr + lenAddr.
  (* Lemma minAddr_rep : (N.of_nat minAddr < bv.exp2 16)%N. *)
  (* Proof. now compute. Qed. *)
  (* Lemma maxAddr_rep : (N.of_nat maxAddr < bv.exp2 16)%N. *)
  (* Proof. now compute. Qed. *)
  (* Lemma lenAddr_rep : (N.of_nat lenAddr < bv.exp2 16)%N. *)
  (* Proof. now compute. Qed. *)
  (* (* 16 is made opaque further on and it really must be non-zero. *) *)
  (* Lemma xlenbits_pos : (16 > 0). *)
  (* Proof. cbv. lia. Qed. *)
  (* All addresses present in RAM memory *)
  Definition liveAddrs := bv.seqBv (@bv.of_nat 16 minAddr) lenAddr.

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

    Axiom pure_decode : bv 16 -> ast.
    Definition interp_ptstoinstr (addr : Address) (id : instr_or_data) : iProp Σ :=
      (∃ v, @interp_ptstomem 2 addr v
              ∗ ⌜ match id with
                  | D _ => True
                  | I i => pure_decode v = i
                  end ⌝)%I.

  End WithSailGS.

  Section MSP430IrisPredicates.

    Import env.notations.

    Equations(noeqns) luser_inst `{sailRegGS Σ, invGS Σ, mcMemGS Σ}
      (p : Predicate) (ts : Env Val (𝑯_Ty p)) : iProp Σ :=
    | accessible_addresses         | [ segb1; segb2 ]       => interp_accessible_addresses segb1 segb2
    | accessible_addresses_without | [ segb1; segb2; addr ] => interp_accessible_addresses_without segb1 segb2 addr
    | instr_arg                    | [ _ ]                  => True
    | encodes_instr                | [ code; instr ]        => ⌜ pure_decode code = instr ⌝%I
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

  (*
  Section RiscVPmpIrisInstanceProofs.
    Context `{sr : sailRegGS Σ} `{igs : invGS Σ} `{mG : mcMemGS Σ}.

    (* Note that the condition on overflow is required: some illegal set-ups are accepted by `pmp_match_addr` as it does not track overflow, and shrinking those might make the output go from match to no match. *)
    Lemma pmp_match_addr_reduced_width (bytes w : Xlenbits) :
      forall paddr rng,
        (bv.bin paddr + bv.bin bytes < bv.exp2 16)%N ->
        bv.zero <ᵘ w ->
        w <=ᵘ bytes ->
        pmp_match_addr paddr bytes rng = PMP_Match ->
        pmp_match_addr paddr w rng = PMP_Match.
    Proof.
      destruct rng as [[lo hi]|]; last by simpl.
      rewrite !pmp_match_addr_match.
      solve_bv.
    Qed.

    Lemma pmp_match_addr_reduced_width_no_match (bytes w : Xlenbits) :
      forall paddr rng,
      (bv.bin paddr + bv.bin bytes < bv.exp2 16)%N ->
      w <=ᵘ bytes ->
      pmp_match_addr paddr bytes rng = PMP_NoMatch ->
      pmp_match_addr paddr w rng = PMP_NoMatch.
    Proof.
      intros paddr [[lo hi]|] Hass Hle; last by simpl.
      rewrite !pmp_match_addr_nomatch.
      intros [|Hcond]; try discriminate. right. intros ? ? Hinv.
      specialize (Hcond _ _ Hinv). inversion Hinv.
      solve_bv.
    Qed.

    Lemma pmp_match_entry_reduced_width (bytes w : Xlenbits) :
      forall paddr cfg p hi lo,
        (bv.bin paddr + bv.bin bytes < bv.exp2 16)%N ->
        bv.zero <ᵘ w ->
        w <=ᵘ bytes ->
        pmp_match_entry paddr bytes p cfg hi lo = PMP_Success ->
        pmp_match_entry paddr w p cfg hi lo = PMP_Success.
    Proof.
      unfold pmp_match_entry.
      intros.
      destruct (pmp_match_addr paddr bytes _) eqn:E; try discriminate.
      apply pmp_match_addr_reduced_width with (w := w) in E; auto.
      now rewrite E.
    Qed.

    Lemma pmp_match_entry_reduced_width_continue (bytes w : Xlenbits) :
      forall paddr cfg p hi lo,
        (bv.bin paddr + bv.bin bytes < bv.exp2 16)%N ->
        w <=ᵘ bytes ->
        pmp_match_entry paddr bytes p cfg hi lo = PMP_Continue ->
        pmp_match_entry paddr w p cfg hi lo = PMP_Continue.
    Proof.
      unfold pmp_match_entry.
      intros.
      destruct (pmp_match_addr paddr bytes _) eqn:E; try discriminate.
      apply pmp_match_addr_reduced_width_no_match with (w := w) in E; auto.
      now rewrite E.
    Qed.

    Lemma pmp_check_aux_access_reduced_width (bytes w : Xlenbits) :
      forall paddr lo entries p acc,
        (bv.bin paddr + bv.bin bytes < bv.exp2 16)%N ->
        bv.zero <ᵘ w ->
        w <=ᵘ bytes ->
        pmp_check_aux paddr bytes lo entries p acc = true ->
        pmp_check_aux paddr w lo entries p acc = true.
    Proof.
      intros paddr lo entries p acc Hrep H0w Hle H.
      generalize dependent lo.
      induction entries as [|[cfg0 hi] es IHentries];
        intros;
        first now simpl in *.
      cbn in *.
      destruct (pmp_match_entry paddr bytes _ _ _ _) eqn:E; last done.
      - apply pmp_match_entry_reduced_width with (w := w) in E; auto.
        now rewrite E.
      - apply pmp_match_entry_reduced_width_continue with (w := w) in E; auto.
        rewrite E.
        unfold pmp_check_aux in IHentries.
        now apply IHentries.
    Qed.

    Lemma pmp_check_access_reduced_width (bytes w : Xlenbits) :
      forall paddr entries p acc,
        (bv.bin paddr + bv.bin bytes < bv.exp2 16)%N ->
        bv.zero <ᵘ w ->
        w <=ᵘ bytes ->
        pmp_check paddr bytes entries p acc = true ->
        pmp_check paddr w entries p acc = true.
    Proof.
      unfold pmp_check; intros;
        apply pmp_check_aux_access_reduced_width with (bytes := bytes); auto.
    Qed.

    Lemma pmp_access_reduced_width (bytes w : Xlenbits) :
      forall paddr pmp p acc ,
        (bv.bin paddr + bv.bin bytes < bv.exp2 16)%N ->
        bv.zero <ᵘ w ->
        w <=ᵘ bytes ->
        Pmp_access paddr bytes pmp p acc ->
        Pmp_access paddr w pmp p acc.
    Proof.
      unfold Pmp_access, Gen_Pmp_access; intros;
        apply pmp_check_aux_access_reduced_width with (bytes := bytes); auto.
    Qed.

    Lemma pmp_match_addr_addr_S_width_pred (bytes : nat) : forall paddr rng res,
        (0 < @bv.bin 16 (bv.of_nat bytes))%N ->
        (bv.bin paddr + N.of_nat (S bytes) < bv.exp2 16)%N ->
        res = PMP_NoMatch ∨ res = PMP_Match ->
        pmp_match_addr paddr (bv.of_nat (S bytes)) rng = res ->
        pmp_match_addr (paddr + bv.one) (bv.of_nat bytes) rng = res.
    Proof.
      intros paddr rng res Hb Hrep.
      destruct rng as [[lo hi]|]; subst; auto.
      intros [Hres|Hres]; subst.
      - rewrite !pmp_match_addr_nomatch. intros [|Hcond]; first discriminate. right.
        intros ? ? Hspec. specialize (Hcond _ _ Hspec). solve_bv.
      - rewrite !pmp_match_addr_match. solve_bv.
    Qed.

    Lemma pmp_match_entry_addr_S_width_pred_success (bytes : nat) : forall paddr p cfg lo hi,
        (0 < @bv.bin 16 (bv.of_nat bytes))%N ->
        (bv.bin paddr + N.of_nat (S bytes) < bv.exp2 16)%N ->
        pmp_match_entry paddr (bv.of_nat (S bytes)) p cfg lo hi = PMP_Success ->
        pmp_match_entry (paddr + bv.one) (bv.of_nat bytes) p cfg lo hi = PMP_Success.
    Proof.
      intros paddr p cfg lo hi Hb Hrep.
      unfold pmp_match_entry.
      intros H.
      destruct (pmp_match_addr paddr _ _) eqn:E;
        apply pmp_match_addr_addr_S_width_pred in E;
        auto;
        try now rewrite E.
      discriminate H.
    Qed.

    Lemma pmp_match_entry_addr_S_width_pred_continue (bytes : nat) : forall paddr p cfg lo hi,
        (0 < @bv.bin 16 (bv.of_nat bytes))%N ->
        (bv.bin paddr + N.of_nat (S bytes) < bv.exp2 16)%N ->
        pmp_match_entry paddr (bv.of_nat (S bytes)) p cfg lo hi = PMP_Continue ->
        pmp_match_entry (paddr + bv.one) (bv.of_nat bytes) p cfg lo hi = PMP_Continue.
    Proof.
      intros paddr p cfg lo hi Hb Hrep.
      unfold pmp_match_entry.
      intros H.
      destruct (pmp_match_addr paddr _ _) eqn:E;
        apply pmp_match_addr_addr_S_width_pred in E;
        auto;
        try now rewrite E.
      discriminate H.
    Qed.

    Lemma pmp_check_aux_addr_S_width_pred (bytes : nat) : forall paddr lo entries p acc,
        (0 < @bv.bin 16 (bv.of_nat bytes))%N ->
        (bv.bin paddr + N.of_nat (S bytes) < bv.exp2 16)%N ->
        pmp_check_aux paddr (bv.of_nat (S bytes)) lo entries p acc = true ->
        pmp_check_aux (paddr + bv.one) (bv.of_nat bytes) lo entries p acc = true.
    Proof.
      intros paddr lo entries p acc Hb Hrep.
      generalize dependent lo.
      induction entries as [|[cfg0 hi] entries IHentries];
        intros;
        first now simpl in *.
      unfold pmp_check_aux.
      unfold pmp_check_aux in H.
      simpl in *.
      destruct (pmp_match_entry paddr _ _ cfg0 _ _) eqn:Ecfg0; auto.
      apply pmp_match_entry_addr_S_width_pred_success in Ecfg0; auto.
      now rewrite Ecfg0.
      apply pmp_match_entry_addr_S_width_pred_continue in Ecfg0; auto.
      rewrite Ecfg0.
      now apply IHentries.
    Qed.

    Lemma pmp_access_addr_S_width_pred (bytes : nat) : forall paddr lo entries p acc,
        (0 < @bv.bin 16 (bv.of_nat bytes))%N ->
        (bv.bin paddr + N.of_nat (S bytes) < bv.exp2 16)%N ->
        Gen_Pmp_access paddr (bv.of_nat (S bytes)) lo entries p acc ->
        Gen_Pmp_access (paddr + bv.one) (bv.of_nat bytes) lo entries p acc.
    Proof.
      intros paddr lo pmp p acc Hb Hrep.
      unfold Gen_Pmp_access.
      now apply pmp_check_aux_addr_S_width_pred.
    Qed.

    Lemma gen_pmp_access_shift (bytes shift: nat) paddr lo entries p acc:
        (0 < @bv.bin 16 (bv.of_nat bytes))%N ->
        (bv.bin paddr + N.of_nat (bytes + shift) < bv.exp2 16)%N ->
        Gen_Pmp_access paddr (bv.of_nat (bytes + shift)) lo entries p acc ->
        Gen_Pmp_access (paddr + bv.of_nat shift) (bv.of_nat bytes) lo entries p acc.
    Proof.
      intros Hzero. generalize dependent paddr.
      induction shift; intros paddr Hrep Hacc.
      - rewrite bv.add_zero_r. rewrite Nat.add_0_r in Hacc. auto.
      - rewrite Nat.add_succ_r in Hacc,Hrep.
        rewrite Nat2N.inj_succ in Hrep.
        apply pmp_access_addr_S_width_pred in Hacc; try solve_bv.
        apply IHshift in Hacc.
          + rewrite bv.of_nat_S bv.add_assoc. apply Hacc.
          + solve_bv.
    Qed.

    Lemma pmp_access_shift (bytes shift: nat) paddr entries p acc:
        (0 < @bv.bin 16 (bv.of_nat bytes))%N ->
        (bv.bin paddr + N.of_nat (bytes + shift) < bv.exp2 16)%N ->
        Pmp_access paddr (bv.of_nat (bytes + shift)) entries p acc ->
        Pmp_access (paddr + bv.of_nat shift) (bv.of_nat bytes) entries p acc.
    Proof. apply gen_pmp_access_shift. Qed.

    (* Use `seqBv` to get rid of conditions on width *)
    (* TODO: intermediate lemma without seqBv that does shift + restrict? *)
    Lemma pmp_seqBv_restrict base width k y entries m p:
      (bv.bin base + N.of_nat width < bv.exp2 16)%N →
      bv.seqBv base width !! k = Some y →
      Pmp_access base (bv.of_nat width) entries m p →
      Pmp_access y (bv.of_nat 1) entries m p.
    Proof.
      intros Hrep Hlkup Hacc.
      pose proof (bv.seqBv_width_at_least _ _ Hlkup) as [p' ->].
      apply bv.seqBv_spec in Hlkup; subst y.
      apply (pmp_access_reduced_width (w := bv.of_nat (1%nat + k))) in Hacc; try solve_bv.
      apply pmp_access_shift in Hacc; solve_bv.
    Qed.

    Lemma addr_in_all_addrs (a : Address): a ∈ all_addrs.
    Proof.
      rewrite all_addrs_eq.
      apply bv.in_seqBv'; unfold bv.ule, bv.ult.
      - cbn. lia.
      - pose proof (bv.bv_is_wf a) as Hwf.
        eapply N.lt_le_trans; [exact|].
        rewrite Nat2N.inj_pow.
        lia.
    Qed.

    Local Lemma to_nat_mono (a b : N) : (a < b)%N → N.to_nat a < N.to_nat b.
    Proof. lia. Qed.
    Lemma in_allAddrs_split (addr : Address) (bytes : nat) :
      (bv.bin addr + N.of_nat bytes < bv.exp2 16)%N ->
      exists l1 l2, all_addrs = l1 ++ (bv.seqBv addr bytes  ++ l2).
    Proof. intros Hrep. rewrite all_addrs_eq.
           refine (bv.seqBv_sub_list _ _); first solve_bv.
           apply to_nat_mono in Hrep.
           rewrite N2Nat.inj_add N2Nat.inj_pow !Nat2N.id in Hrep.
           apply Nat.lt_le_incl, (Nat.lt_le_trans _ _ _ Hrep).
           now compute -[Nat.pow].
    Qed.

    Lemma ptstoSthL_app {l1 l2} : (ptstoSthL (l1 ++ l2) ⊣⊢ ptstoSthL l1 ∗ ptstoSthL l2)%I.
    Proof. eapply big_sepL_app. Qed.

    Lemma ptstomem_bv_app :
      forall {n} (a : Address) (b : bv byte) (bs : bv (n * byte)),
        @interp_ptstomem _ _ (S n)%nat a (bv.app b bs)
        ⊣⊢
        (interp_ptsto a b ∗ interp_ptstomem (bv.one + a) bs).
    Proof. intros; cbn [interp_ptstomem]; now rewrite bv.appView_app. Qed.

    Lemma pmp_entries_ptsto : ∀ (entries : list PmpEntryCfg),
        interp_pmp_entries entries ⊣⊢
          ∃ (cfg0 : Pmpcfg_ent) (addr0 : Address) (cfg1 : Pmpcfg_ent) (addr1 : Address),
            ⌜entries = [(cfg0, addr0); (cfg1, addr1)]⌝ ∗
            reg_pointsTo pmp0cfg cfg0 ∗ reg_pointsTo pmpaddr0 addr0 ∗
            reg_pointsTo pmp1cfg cfg1 ∗ reg_pointsTo pmpaddr1 addr1.
    Proof.
      intros entries; iSplit; iIntros  "H".
      - unfold interp_pmp_entries.
        destruct entries as [|[cfg0 addr0] [|[cfg1 addr1] [|]]] eqn:?; try done.
        repeat iExists _.
        now iFrame.
     -  iDestruct "H" as "(% & % & % & % & -> & ? & ? & ? & ?)"; iFrame.
    Qed.

    Lemma interp_ptstomem_exists_intro (bytes : nat) :
      ⊢ ∀ (paddr : Address) (w : bv (bytes * byte)),
          interp_ptstomem paddr w -∗
          ∃ (w : bv (bytes * byte)), interp_ptstomem paddr w.
    Proof. auto. Qed.

    Lemma interp_ptstomem_big_sepS (bytes : nat) (paddr : Address):
      (∃ (w : bv (bytes * byte)), interp_ptstomem paddr w) ⊣⊢
        ptstoSthL (bv.seqBv paddr bytes).
    Proof.
      generalize dependent paddr.
      iInduction bytes as [|bytes] "IHbytes"; iIntros (paddr).
      - unfold ptstoSthL. unshelve auto. exact bv.zero.
      - rewrite bv.seqBv_succ (app_comm_cons []) ptstoSthL_app.
        iDestruct ("IHbytes" $! (bv.one + paddr)) as "[IHL IHR]".
        iSplit.
        *  iIntros "[%w H]".
           destruct (bv.appView byte (bytes * byte) w) as [b bs].
           rewrite ptstomem_bv_app.
           iDestruct "H" as "[Hb Hbs]".
           iSplitL "Hb".
           + cbn. iSplit; [by iExists _ | auto].
           + iApply "IHL"; by iExists _.
        * iIntros "[[[%b Hhd] _] Htl]".
          iDestruct ("IHR" with "Htl") as "[%btl Htl]".
          iExists (bv.app b btl).
          rewrite ptstomem_bv_app. iFrame.
    Qed.

    Lemma interp_addr_access_app base width width':
      interp_addr_access liveAddrs mmioAddrs base (width + width') ⊣⊢
      interp_addr_access liveAddrs mmioAddrs base width ∗ interp_addr_access liveAddrs mmioAddrs (base + bv.of_nat width) width'.
    Proof.
      unfold interp_addr_access.
      by rewrite bv.seqBv_app big_sepL_app.
    Qed.

    Lemma interp_addr_access_cons base width:
      interp_addr_access liveAddrs mmioAddrs base (S width) ⊣⊢
      interp_addr_access_byte liveAddrs mmioAddrs base ∗ interp_addr_access liveAddrs mmioAddrs (base + bv.of_nat 1) width.
    Proof. rewrite <-Nat.add_1_l.
           rewrite interp_addr_access_app.
           unfold interp_addr_access, interp_addr_access_byte.
           by rewrite bv.seqBv_one big_sepL_singleton.
    Qed.

    Lemma interp_addr_access_single base:
      interp_addr_access liveAddrs mmioAddrs base 1 ⊣⊢
      interp_addr_access_byte liveAddrs mmioAddrs base.
    Proof. rewrite interp_addr_access_cons.
           iSplit; iIntros "H"; [iDestruct "H" as "[H _]"|]; iFrame.
           unfold interp_addr_access. now cbn.
    Qed.

    (* Induction does not work here due to shape of `interp_pmp_addr_access_without`*)
    Lemma interp_pmp_addr_inj_extr {entries m p} base width :
      (bv.bin base + N.of_nat width < bv.exp2 16)%N →
      Pmp_access base (bv.of_nat width) entries m p →
      (interp_pmp_addr_access liveAddrs mmioAddrs entries m ⊣⊢
      (interp_addr_access liveAddrs mmioAddrs base width ∗ interp_pmp_addr_access_without liveAddrs mmioAddrs base width entries m))%I.
    Proof.
      intros Hrep Hpmp.
      (* Discharge easy direction *)
      iSplit ; last (iIntros "[H Hcont]"; by iApply "Hcont").
      unfold interp_pmp_addr_access_without, interp_pmp_addr_access.
      (* Hard direction: create `interp_addr_access` from scratch *)
      unfold interp_pmp_addr_access.
      pose proof (in_allAddrs_split base width Hrep) as [l1 [l2 Hall]]. rewrite Hall.
      rewrite !big_sepL_app.
      iIntros "(Hlow & Hia & Hhigh)".
      iSplitL "Hia".
      - iApply (big_sepL_mono with "Hia"). iIntros (? ? ?) "Hyp".
        iApply "Hyp". iPureIntro.
        eexists; eapply pmp_seqBv_restrict; eauto.
      - iIntros "Hia". iFrame.
        iDestruct (big_sepL_mono with "Hia") as "Hia"; last iFrame.
        now iIntros.
      Qed.

    Lemma interp_pmp_within_mmio_spec {entries m p} (paddr : Address) bytes :
      (bv.bin paddr + N.of_nat bytes < bv.exp2 16)%N ->
      Pmp_access paddr (bv.of_nat bytes) entries m p →
      interp_pmp_addr_access liveAddrs mmioAddrs entries m -∗
      ⌜bool_decide (withinMMIO paddr bytes) = false%nat⌝.
    Proof.
      iIntros (Hrep Hpmp) "Hint".
      destruct bytes as [|bytes]. (* No induction needed: disproving one location suffices. *)
      - cbn - [16] in *. rewrite bool_decide_eq_false. iPureIntro. by intro HFalse.
      - rewrite interp_pmp_addr_inj_extr; eauto.
        iDestruct "Hint" as "[Hint _]".
        iDestruct (interp_addr_access_cons with "Hint") as "[Hfirst _]".
        unfold interp_addr_access_byte.
        case_decide; auto.
        iPureIntro.
        rewrite bool_decide_eq_false /withinMMIO.
        destruct bytes; first congruence.
        rewrite !not_and_l. left; congruence.
    Qed.

    (* Bidirectional version of the Iris lemma *)
    Lemma big_sepL_mono_iff {PROP : bi} {A : Type} (Φ Ψ : nat → A → PROP) (l : list A) :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊣⊢ [∗ list] k ↦ y ∈ l, Ψ k y.
    Proof.
      intros Hiff.
      iSplit; iApply big_sepL_mono; iIntros; iApply Hiff; auto.
    Qed.

    (* Use knowledge of RAM to extract byte *)
    Lemma interp_addr_access_byte_extr  base :
      base ∈ liveAddrs ->
      (interp_addr_access_byte liveAddrs mmioAddrs base ⊢
      ptstoSth base).
    Proof.
      intros (* Hpmp *) Hlive.
      unfold interp_addr_access_byte, ptstoSth, interp_ptsto.
      repeat case_decide; auto; iIntros; by exfalso.
    Qed.

    (* Inserting a byte is always possible *)
    Lemma interp_addr_access_byte_inj base :
       ptstoSth base -∗ interp_addr_access_byte liveAddrs mmioAddrs base.
    Proof.
      unfold interp_addr_access_byte, ptstoSth, interp_ptsto.
      iIntros "HFalse". iDestruct "HFalse" as (?) "[Hmapsto %HFalse]".
      case_decide.
      - by cbn in HFalse.
      - case_decide; auto.
    Qed.

    (* Use knowledge of RAM to extract range *)
    Lemma interp_addr_access_extr base width :
      (minAddr ≤ N.to_nat (bv.bin base)) →
      (N.to_nat (bv.bin base) + width ≤ maxAddr) →
      (bv.bin base + N.of_nat width < bv.exp2 16)%N →
      interp_addr_access liveAddrs mmioAddrs base width ⊢
      (∃ (w : bv (width * byte)), interp_ptstomem base w).
    Proof.
      intros HminOK HmaxOK Hrep.
      rewrite interp_ptstomem_big_sepS.
      unfold interp_addr_access, ptstoSthL.
      iApply big_sepL_mono.
      iIntros (? y Hseq) "//".
      iApply interp_addr_access_byte_extr.
      apply bv.seqBv_spec in Hseq as Hspec.
      apply list.lookup_lt_Some in Hseq. rewrite bv.seqBv_len in Hseq.
      unfold liveAddrs, bv.seqBv.
      rewrite -(bv.of_Z_unsigned y).
      apply elem_of_list_fmap_1.
      rewrite elem_of_seqZ.
      subst y.
      unfold maxAddr in HmaxOK.
      rewrite /bv.unsigned bv.bin_add_small !bv.bin_of_nat_small; lia. (* TODO: use representability of min/maxAddr here, once they are made properly opaque *)
    Qed.

    (* Inserting a range is always possible *)
    Lemma interp_addr_access_inj base width:
      (∃ (w : bv (width * byte)), interp_ptstomem base w) ⊢
      interp_addr_access liveAddrs mmioAddrs base width.
    Proof.
      iIntros "Hint".
      rewrite interp_ptstomem_big_sepS.
      unfold interp_addr_access, ptstoSthL.
      iApply big_sepL_mono; last auto.
      iIntros (? y Hseq) "/=".
      iApply interp_addr_access_byte_inj.
    Qed.

    (* TODO: This lemma is not a special case of the above, because of strange semantics of `Pmp_access`*)
    Lemma interp_pmp_addr_access_without_0 {entries m} base :
      interp_pmp_addr_access liveAddrs mmioAddrs entries m ⊣⊢ interp_pmp_addr_access_without liveAddrs mmioAddrs base 0 entries m.
    Proof. unfold interp_pmp_addr_access_without, interp_addr_access.
           rewrite bv.seqBv_zero.
           iSplit; iIntros "H".
           - now iIntros "_".
           - now iApply "H".
    Qed.

  End RiscVPmpIrisInstanceProofs. *)

  Include IrisSignatureRules MSP430Base MSP430Signature MSP430Program
    MSP430Semantics MSP430IrisBase.
  Include IrisAdequacy MSP430Base MSP430Signature MSP430Program
    MSP430Semantics MSP430IrisBase MSP430IrisAdeqParameters.

End MSP430IrisInstance.
