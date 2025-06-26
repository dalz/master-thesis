From Coq Require Import
  ZArith.ZArith
  Lists.List
  Strings.String.
From Katamaran Require Import
  Bitvector
  Notations
  Specification
  SmallStep.Step.
Require Import
  BlockVer.Spec
  BlockVer.Verifier
  IrisModel
  IrisInstance
  Machine
  Sig
  BootcodeBlocks
  LoopVerification
  Contracts.

From iris.base_logic Require lib.gen_heap lib.iprop invariants.
From iris.bi Require interface big_op.
From iris.algebra Require dfrac big_op.
From iris.program_logic Require weakestpre adequacy.
From iris.proofmode Require string_ident tactics.
From stdpp Require namespaces.
Import iris.bi.big_op.
Import iris.algebra.big_op.
Import iris.program_logic.weakestpre.
Import iris.proofmode.tactics.

Open Scope ctx_scope.
Set Implicit Arguments.

Import ctx.resolution.
Import ctx.notations.
Import env.notations.
Import ListNotations.

Import Contracts.
Import MSP430BlockVerifShalExecutor.
Import MSP430BlockVerifSpec.
Import MSP430IrisAdeqParameters.
Import MSP430IrisBase.
Import MSP430IrisInstance.
Import MSP430Program.
Import MSP430Semantics.
Import MicroSail.ShallowExecutor.
Import SmallStepNotations.
Import ctx.notations.
Import ctx.resolution.
Import env.notations.

Module inv := invariants.

Section Bootcode.
  Import bv.notations.
  Import ListNotations.
  Import TermNotations.
  Import Spec.Assembly.
  Import BootcodeBlocks.

  Open Scope hex_Z_scope.

  Ltac iIntros_anon :=
    iIntros "H"; repeat iDestruct "H" as "[? H]"; iDestruct "H" as "?".

  Definition ipectl : bv 16 := [bv 0xC0]. (* enabled and locked *)
  Definition segb1 : bv 16 := [bv 0x4] .  (* * 16 = 0x40 *)
  Definition segb2 : bv 16 := [bv 0x5].   (* * 16 = 0x50 *)
  Definition data_addr : bv 16 := [bv 0x4A].
  Definition data_size := Z.to_nat (maxAddr - bv.unsigned (end_addr))%Z.

  Definition inv_fortytwo `{sailGS Σ} : iProp Σ :=
    interp_ptsto_readonly data_addr [bv 42].

  (* unprotected addresses, excluding bootcode which should be in ROM or smth *)
  Definition advAddrs1 :=
    bv.seqBv end_addr (Z.to_nat (bv.unsigned segb1 * 16 - bv.unsigned end_addr))%Z.
  Definition advAddrs2 :=
    bv.seqBv (bv.shiftl segb2 [bv [3] 4]) (Z.to_nat (maxAddr - bv.unsigned segb2 * 16))%Z.
  Definition advAddrs : list _ := advAddrs1 ++ advAddrs2.

  Definition block_mass_erase : list ast_with_args :=
    [FAIL] ++ repeat (mov_rr CG2 CG2) 5.

  Definition mem_has_word (μ : Memory) (a : Val ty.wordBits) (w : Val ty.wordBits) : Prop :=
    exists v0 v1, map μ (bv.seqBv a 2) = [v0; v1]%list /\ bv.app v0 v1 = w.

  Definition mem_has_instr (μ : Memory) (a : Val ty.wordBits) (instr : ast) : Prop :=
    exists w, mem_has_word μ a w /\ pure_decode (Word w) = inr instr.

  Fixpoint mem_has_instrs (μ : Memory) (a : Val ty.wordBits) (instrs : list ast_with_args) : Prop :=
    match instrs with
    | instr :: instrs =>
        mem_has_instr μ a (instr_without_args instr)
        /\ match instr with
           | I0 _ =>
               mem_has_instrs μ (a + [bv 2]) instrs
           | I1 _ x =>
               mem_has_word μ (a + [bv 2]) x
               /\ mem_has_instrs μ (a + [bv 4]) instrs
           | I2 _ x y =>
               mem_has_word μ (a + [bv 2]) x
               /\ mem_has_word μ (a + [bv 4]) y
               /\ mem_has_instrs μ (a + [bv 6]) instrs
           end%bv
    | [] => True
    end%list.

  Local Notation "r '↦' val" := (reg_pointsTo r val) (at level 70).

  Definition minimal_pre `{sailGS Σ} : iProp Σ :=
    (∃ v, LastInstructionFetch ↦ v) ∗
    (∃ v, SRCG1_reg ↦ v) ∗
    MPUCTL0_reg ↦ [bv 0xA500].

  Definition minimal_post `{sailGS Σ} := minimal_pre.

  Definition make_contract `{sailGS Σ} pre post : iProp Σ :=
    (minimal_pre ∗ pre) -∗
    (minimal_post ∗ post -∗ WP_loop) -∗
    WP_loop.

  Definition ipe_register_init `{sailGS Σ} : iProp Σ :=
    MPUIPC0_reg ↦ [bv 0]
    ∗ (∃ v, MPUIPSEGB1_reg ↦ v)
    ∗ (∃ v, MPUIPSEGB2_reg ↦ v).

  Definition start_bootcode_pre `{sailGS Σ} : iProp Σ :=
    PC_reg ↦ start_bootcode_start
    ∗ ptsto_instrs start_bootcode_start block_start_bootcode
    ∗ ipe_register_init
    ∗ R10_reg ↦ saved_ptr_bv
    ∗ (ptsto_word saved_ptr_bv [bv 0]
       ∨ ptsto_word saved_ptr_bv isp_bv).

  Definition start_bootcode_post `{sailGS Σ} : iProp Σ :=
    ipe_register_init
    ∗ ptsto_instrs start_bootcode_start block_start_bootcode
    ∗ R10_reg ↦ saved_ptr_bv
    ∗ (ptsto_word saved_ptr_bv [bv 0] ∗ PC_reg ↦ transfer_if_valid_struct_start
       ∨ ptsto_word saved_ptr_bv isp_bv ∗ PC_reg ↦ check_struct_start).

  Definition contract_start_bootcode `{sailGS Σ} : iProp Σ :=
    make_contract start_bootcode_pre start_bootcode_post.

  Lemma start_bootcode_verified `{sailGS Σ} : ⊢ contract_start_bootcode.
  Proof.
    iIntros "Hpre Hk".
    iApply (sound_sblock_verification_condition valid_start_bootcode [env]
              $! start_bootcode_start with "[Hpre] [Hk]").
    - unfold start_bootcode_pre, minimal_pre. cbn -[ptsto_instrs].
      iDestruct "Hpre" as "((% & ? & % & ? & ?) & ? & ? & ? & ? & H0)".
      iFrame.
      rewrite !bi.sep_True !bi.and_emp.
      cbv [bv.app bv.fold_right bv.bv_case bv.cons bv.wf_double].
      iDestruct "H0" as "[H0 | H0]".
      + iSplitL "". done. iLeft. by iSplitR.
      + iSplitL "". done. iRight. by iSplitR.
    - cbn.
      iIntros (an) "(? & [? ?] & (? & ? & ?) & (? & ? & [((_ & [? _] & [? _]) & -> & _) | ((_ & [? _] & [? _]) & -> & _)]))";
        iApply ("Hk" with "[-]"); iFrame; [iLeft | iRight]; iFrame.
  Qed.

  Definition transfer_if_valid_struct_pre `{sailGS Σ} : iProp Σ :=
    PC_reg ↦ transfer_if_valid_struct_start
    ∗ ptsto_instrs transfer_if_valid_struct_start block_transfer_if_valid_struct

    ∗ ipe_register_init
    ∗ R10_reg ↦ saved_ptr_bv
    ∗ R11_reg ↦ valid_flag_bv
    ∗ R12_reg ↦ ipe_sig_valid_src_bv
    ∗ R13_reg ↦ ipe_struct_pointer_src_bv

    ∗ ptsto_word ipe_sig_valid_src_bv valid_flag_bv
    ∗ ptsto_word ipe_struct_pointer_src_bv isp_bv
    ∗ ptsto_word saved_ptr_bv [bv 0].

  Definition transfer_if_valid_struct_post `{sailGS Σ} : iProp Σ :=
    PC_reg ↦ check_struct_start
    ∗ ptsto_instrs transfer_if_valid_struct_start block_transfer_if_valid_struct

    ∗ ipe_register_init
    ∗ R10_reg ↦ saved_ptr_bv
    ∗ R11_reg ↦ valid_flag_bv
    ∗ R12_reg ↦ ipe_sig_valid_src_bv
    ∗ R13_reg ↦ ipe_struct_pointer_src_bv

    ∗ ptsto_word ipe_sig_valid_src_bv valid_flag_bv
    ∗ ptsto_word ipe_struct_pointer_src_bv isp_bv
    ∗ ptsto_word saved_ptr_bv isp_bv.

  Definition contract_transfer_if_valid_struct `{sailGS Σ} : iProp Σ :=
    make_contract transfer_if_valid_struct_pre transfer_if_valid_struct_post.

  Lemma transfer_if_valid_struct_verified `{sailGS Σ} : ⊢ contract_transfer_if_valid_struct.
  Proof.
    iIntros "Hpre Hk".
    iApply (sound_sblock_verification_condition valid_transfer_if_valid_struct [env]
              $! transfer_if_valid_struct_start with "[Hpre] [Hk]").
    - unfold transfer_if_valid_struct_pre, minimal_pre. cbn -[ptsto_instrs].
      iDestruct "Hpre" as "((% & ? & % & ? & ?) &? & ? & ? & ? & ? & ? & ? & [? ?] & [? ?] & ? & [? ?])".
      now iFrame.
    - cbn.
      iIntros (an) "(? & (? & ? & ? & ? & _) & (? & ? & ?) & [-> _] & (? & ? & ?) & ? & ? & ? & ? & (? & [? _] & [? _]) & (? & [? _] & [? _]) & (? & [? _] & [? _]))".
      iApply ("Hk" with "[$]").
  Qed.

  Definition check_struct_pre `{sailGS Σ} (ipectl segb1 segb2 check : bv 16) : iProp Σ :=
    PC_reg ↦ check_struct_start
    ∗ ptsto_instrs check_struct_start block_check_struct

    ∗ ipe_register_init
    ∗ R10_reg ↦ saved_ptr_bv
    ∗ R15_reg ↦ [bv 0xFFFF]
    ∗ (∃ v, R6_reg ↦ v)
    ∗ (∃ v, R14_reg ↦ v)

    ∗ ptsto_word saved_ptr_bv isp_bv

    ∗ ptsto_word isp_bv ipectl
    ∗ ptsto_word (isp_bv + [bv 2])%bv segb2
    ∗ ptsto_word (isp_bv + [bv 4])%bv segb1
    ∗ ptsto_word (isp_bv + [bv 6])%bv check.

  Definition check_struct_post `{sailGS Σ} (ipectl segb1 segb2 check : bv 16) : iProp Σ :=
    (PC_reg ↦ evaluate_struct_start
     ∨ PC_reg ↦ mass_erase_start)
    ∗ ptsto_instrs check_struct_start block_check_struct

    ∗ ipe_register_init
    ∗ R10_reg ↦ saved_ptr_bv
    ∗ R15_reg ↦ [bv 0xFFFF]
    ∗ R6_reg ↦ (isp_bv + [bv 6])%bv
    ∗ (∃ v, R14_reg ↦ v)

    ∗ ptsto_word saved_ptr_bv isp_bv

    ∗ ptsto_word isp_bv ipectl
    ∗ ptsto_word (isp_bv + [bv 2])%bv segb2
    ∗ ptsto_word (isp_bv + [bv 4])%bv segb1
    ∗ ptsto_word (isp_bv + [bv 6])%bv check.

  Definition contract_check_struct `{sailGS Σ} (ipectl segb1 segb2 check : bv 16) : iProp Σ :=
    make_contract
      (check_struct_pre ipectl segb1 segb2 check)
      (check_struct_post ipectl segb1 segb2 check).

  Lemma ptstomem_subrange_2 `{sailGS Σ} : forall (a b w : bv 16),
      b = (a + [bv 1])%bv ->
      @interp_ptstomem _ _ 2 a w ⊣⊢
        @interp_ptstomem _ _ 1 a (bv.vector_subrange 0 8 w) ∗
        @interp_ptstomem _ _ 1 b (bv.vector_subrange 8 8 w).
  Proof.
    intros a b w ->.
    iSplit.
    - iIntros "Hw".
      unfold interp_ptstomem.
      destruct bv.appView.
      iDestruct "Hw" as "[Hlo Hhi]".
      iSplitL "Hlo".
      + unfold bv.vector_subrange.
        cbn -[bv.appView].
        rewrite bv.take_app.
        unfold bv.drop.
        destruct (bv.appView 0 8 xs).
        destruct (bv.appView 8 0 ys0).
        destruct ys0, xs.
        unfold bv.is_wf in i, i0.
        destruct bin, bin0;
          destruct i, i0.
        rewrite bv.app_nil bv.app_nil_r.
        cbn. iFrame.
      + unfold bv.vector_subrange.
        cbn -[bv.appView].
        rewrite bv.take_full.
        rewrite bv.drop_app.
        destruct bv.appView.
        rewrite bv.add_comm.
        iFrame.
    - iIntros "[Hlo Hhi]".
      unfold interp_ptstomem.
      destruct (bv.appView 8 (1 * 8) w).
      destruct (bv.appView 8 (0 * 8) ys).
      unfold bv.vector_subrange.
      cbn -[bv.appView interp_ptsto].
      rewrite bv.take_app bv.take_full.
      cbn -[bv.appView interp_ptsto].
      unfold bv.drop.
      destruct (bv.appView 0 8 xs), (bv.appView 8 0 ys0).
      destruct ys0, xs, ys.
      unfold bv.is_wf in i, i0, i1.
      destruct bin, bin0, bin1;
        destruct i, i0, i1.
      rewrite !bv.app_nil !bv.app_nil_r.
      cbn -[bv.appView interp_ptsto].
      rewrite bv.appView_app.
      destruct (bv.appView 8 0 xs0).
      destruct ys. unfold bv.is_wf in i. destruct bin; destruct i.
      rewrite bv.app_nil_r. cbn.
      rewrite !bi.sep_True bv.add_comm. iFrame.
  Qed.

  Lemma check_struct_verified `{sailGS Σ} (ipectl segb1 segb2 check : bv 16) :
    ⊢ contract_check_struct ipectl segb1 segb2 check.
  Proof.
    iIntros "Hpre Hk".
    iApply (sound_sblock_verification_condition valid_check_struct
              [env]
               .[("ipectl_l" :: ty.byteBits) ↦ bv.vector_subrange 0 8 ipectl]
               .[("ipectl_h" :: ty.byteBits) ↦ bv.vector_subrange 8 8 ipectl]
               .[("segb2_l"  :: ty.byteBits) ↦ bv.vector_subrange 0 8 segb2]
               .[("segb2_h"  :: ty.byteBits) ↦ bv.vector_subrange 8 8 segb2]
               .[("segb1_l"  :: ty.byteBits) ↦ bv.vector_subrange 0 8 segb1]
               .[("segb1_h"  :: ty.byteBits) ↦ bv.vector_subrange 8 8 segb1]
               .[("check_l"  :: ty.byteBits) ↦ bv.vector_subrange 0 8 check]
               .[("check_h"  :: ty.byteBits) ↦ bv.vector_subrange 8 8 check]
              $! check_struct_start with "[Hpre] [Hk]").
    - unfold check_struct_pre, minimal_pre.
      cbn -[ptsto_instrs bv.is_wf interp_ptstomem bv.appView].
      iDestruct "Hpre" as "(A & B & C & D & E & F & G & H & I & J & K & L & M)".
      iSplitR "B C"; last iFrame.
      iSplitL "A". iAssumption.
      iSplitR. done.
      unfold ipe_register_init.
      iFrame "D E F G H".
      iSplitL "I". cbn. rewrite !bi.sep_True. by iFrame.
      iSplitL "J". simpl (bv.appView 1 15 isp_bv). cbn iota.
      iSplitR. done.
      { unfold ptsto_word, bv.app. cbn -[interp_ptstomem].
        iApply ptstomem_subrange_2; auto. }
      iSplitL "K". simpl (bv.appView 1 15 (isp_bv + [bv 0x2])%bv). cbn iota.
      iSplitR. done.
      { unfold ptsto_word, bv.app. cbn -[interp_ptstomem].
        iApply ptstomem_subrange_2; auto. }
      iSplitL "L". simpl (bv.appView 1 15 (isp_bv + [bv 0x4])%bv). cbn iota.
      iSplitR. done.
      { unfold ptsto_word, bv.app. cbn -[interp_ptstomem].
        iApply ptstomem_subrange_2; auto. }
      iSplitR. simpl (bv.appView 1 15 (isp_bv + [bv 0x6])%bv). cbn iota.
      iSplit; done.
      unfold ptsto_word, bv.app. cbn -[interp_ptstomem].
      iApply ptstomem_subrange_2; done.
    - cbn -[ptsto_instrs bv.is_wf interp_ptstomem bv.appView].
      simpl (bv.appView 1 15 _%bv). cbn iota.
      iIntros (an) "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15)".
      iApply ("Hk" with "[-]").
      iFrame "H2".
      iSplitL "H0 H3". iDestruct "H3" as "[[-> _] | [-> _]]"; by [iLeft | iRight].
      iFrame "H1 H4 H5 H6 H7 H8".
      iSplitL "H9".
      { iDestruct "H9" as "[_ ?]". iApply ptstomem_subrange_2; auto. }
      iSplitL "H10".
      { iDestruct "H10" as "[_ ?]". iApply ptstomem_subrange_2; auto. }
      iSplitL "H11".
      { iDestruct "H11" as "[_ ?]". iApply ptstomem_subrange_2; auto. }
      iSplitL "H12".
      { iDestruct "H12" as "[_ ?]". iApply ptstomem_subrange_2; auto. }
      iDestruct "H13" as "[_ ?]". iApply ptstomem_subrange_2; auto.
      unfold bv.app. cbn -[interp_ptstomem].
      simpl (bv.cons _ (bv.drop 1 (isp_bv + [bv 0x6]))).
      iFrame.
  Qed.


  Definition evaluate_struct_pre `{sailGS Σ} (ipectl segb1 segb2 : bv 16) : iProp Σ :=
    PC_reg ↦ evaluate_struct_start
    ∗ ptsto_instrs evaluate_struct_start block_evaluate_struct

    ∗ ipe_register_init
    ∗ R6_reg ↦ (isp_bv + [bv 6])%bv
    ∗ R7_reg ↦ MPUIPC0_addr_bv
    ∗ R8_reg ↦ MPUIPSEGB2_addr_bv
    ∗ R9_reg ↦ MPUIPSEGB1_addr_bv

    ∗ ptsto_word (isp_bv + [bv 4])%bv segb1
    ∗ ptsto_word (isp_bv + [bv 2])%bv segb2
    ∗ ptsto_word isp_bv ipectl.

  Definition evaluate_struct_post `{sailGS Σ} (ipectl segb1 segb2 : bv 16) : iProp Σ :=
    PC_reg ↦ end_addr
    ∗ ptsto_instrs evaluate_struct_start block_evaluate_struct

    ∗ MPUIPC0_reg    ↦ ipectl
    ∗ MPUIPSEGB1_reg ↦ segb1
    ∗ MPUIPSEGB2_reg ↦ segb2

    ∗ R6_reg ↦ (isp_bv + [bv 6])%bv
    ∗ R7_reg ↦ MPUIPC0_addr_bv
    ∗ R8_reg ↦ MPUIPSEGB2_addr_bv
    ∗ R9_reg ↦ MPUIPSEGB1_addr_bv

    ∗ ptsto_word (isp_bv + [bv 4])%bv segb1
    ∗ ptsto_word (isp_bv + [bv 2])%bv segb2
    ∗ ptsto_word isp_bv ipectl.

  Definition contract_evaluate_struct `{sailGS Σ} (ipectl segb1 segb2 : bv 16) : iProp Σ :=
    make_contract
      (evaluate_struct_pre ipectl segb1 segb2)
      (evaluate_struct_post ipectl segb1 segb2).
  
  Lemma evaluate_struct_verified `{sailGS Σ} (ipectl segb1 segb2 : bv 16) :
    ⊢ contract_evaluate_struct ipectl segb1 segb2.
  Proof.
    iIntros "Hpre Hk".
    iApply (sound_sblock_verification_condition valid_evaluate_struct
              [env]
                .[("ipectl" :: ty.wordBits) ↦ ipectl]
                .[("segb1"  :: ty.wordBits) ↦ segb1]
                .[("segb2"  :: ty.wordBits) ↦ segb2]
              $! evaluate_struct_start with "[Hpre] [Hk]");
      cbn -[ptsto_instrs bv.is_wf interp_ptstomem bv.appView];
      simpl (bv.appView 1 15 _). cbn iota.

    - iDestruct "Hpre" as "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10)".
      iSplitR "H1 H2"; last iFrame.
      iFrame "H0 H5 H6 H7".
      iSplitR. done.
      iFrame "H3 H4".
      iSplitL "H8"; last iSplitL "H9"; (iSplitR; first done);
        unfold ptsto_word, bv.app; cbn -[interp_ptstomem];
        by iApply ptstomem_subrange_2.
    - iIntros (an) "(H0 & H1 & H2 & [-> _] & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13)".
      iApply ("Hk" with "[-]").
      iFrame "H2 H0 H1 H4 H5 H6 H7 H8 H9 H10".
      iSplitL "H11"; last iSplitL "H12";
        iDestruct select (_)%I as "[_ ?]";
        by iApply ptstomem_subrange_2.
  Qed.

  Definition mass_erase_pre `{sailGS Σ} : iProp Σ :=
    PC_reg ↦ mass_erase_start ∗
    ptsto_instrs mass_erase_start block_mass_erase ∗
    ipe_register_init.

  Definition contract_mass_erase `{sailGS Σ} : iProp Σ :=
    make_contract mass_erase_pre False.

  Section Sym_mass_erase.
    Import asn.notations.
    Local Notation "'{{' P '}}' i '{{' Q '}}'" :=
      (@MkBlockVerifierContract [ctx] P%asn i Q%asn)
        (at level 90, format "'[v' '{{'  P  '}}' '/'  i '/' '{{'  Q  '}}' ']'").

    Definition scontract_mass_erase : BlockVerifierContract :=
      {{
          term_var "a" = term_val ty.Address mass_erase_start ∗
          MPUIPC0_reg ↦ term_val ty.wordBits [bv 0] ∗
          ∃ "v", MPUIPSEGB1_reg ↦ term_var "v" ∗
          ∃ "v", MPUIPSEGB2_reg ↦ term_var "v"
      }}
        block_mass_erase
      {{ ⊥ }}.

    Lemma valid_mass_erase : ValidBlockVerifierContract scontract_mass_erase.
    Proof. now vm_compute. Qed.
  End Sym_mass_erase.


  Lemma mass_erase_verified `{sailGS Σ} : ⊢ contract_mass_erase.
    iIntros "Hpre Hk".
  iApply (sound_sblock_verification_condition valid_mass_erase [env]
            $! mass_erase_start with "[Hpre] [Hk]").
  - unfold mass_erase_pre, minimal_pre. cbn -[ptsto_instrs].
    iDestruct "Hpre" as "(? & ? & ? & ?)".
    now iFrame.
  - cbn. by iIntros (an) "(? & ? & ? & % & ?)".
  Qed.

  Definition registers_not_in_bootcode `{sailGS Σ} : iProp Σ :=
      (∃ v, SP_reg ↦ v)
    ∗ (∃ v, SRCG1_reg ↦ v)
    ∗ (∃ v, CG2_reg ↦ v)
    ∗ (∃ v, R4_reg ↦ v)
    ∗ (∃ v, R5_reg ↦ v)
    ∗ (∃ v, MPUCTL0_reg ↦ v)
    ∗ (∃ v, MPUCTL1_reg ↦ v)
    ∗ (∃ v, MPUSEGB2_reg ↦ v)
    ∗ (∃ v, MPUSEGB1_reg ↦ v)
    ∗ (∃ v, MPUSAM_reg ↦ v)
    ∗ (∃ v, LastInstructionFetch ↦ v).

  Fixpoint code_size (instrs : list ast_with_args) : nat :=
    match instrs with
    | []                 => 0
    | I0 _     :: instrs => 2 + code_size instrs
    | I1 _ _   :: instrs => 4 + code_size instrs
    | I2 _ _ _ :: instrs => 6 + code_size instrs
    end%list%nat.

  (*
  Lemma ptstomem_to_ptstoSth_2 `{sailGS Σ} : forall a w,
      @interp_ptstomem _ _ 2 a w ⊢ ptstoSth a ∗ ptstoSth ([bv [16] 1] + a)%bv.
  Proof.
    iIntros (a w) "Hmem".
    unfold interp_ptstomem.
    repeat destruct bv.appView.
    iDestruct "Hmem" as "(Ha & Ha1 & _)".
    iSplitL "Ha". by iExists xs. by iExists xs0.
  Qed.

  Lemma ptsto_instrs_extract_ptsto `{sailGS Σ} : forall s c,
      ptsto_instrs s c ⊢ ptstoSthL (bv.seqBv s (code_size c)).
  Proof.
    iIntros (s c) "Hinstrs".
    iInduction c as [|[i|i|i]]
forall (s).
    by rewrite bv.seqBv_zero.

       - simpl. rewrite !bv.seqBv_succ.
         unfold ptstoSthL. rewrite !big_sepL_cons.
         unfold interp_ptstoinstr.
         iDestruct "Hinstrs" as "[(% & Hs & _) Hinstrs]".
         rewrite ptstomem_to_ptstoSth_2.
         iDestruct "Hs" as "[$ $]".
         iApply "IHc".
         rewrite bv.add_assoc.
         change (@bv.one 16 + @bv.one 16)%bv with [bv [16] 0x2].
         by rewrite bv.add_comm.
       - simpl. rewrite !bv.seqBv_succ.
         unfold ptstoSthL. rewrite !big_sepL_cons.
         unfold interp_ptstoinstr.
         iDestruct "Hinstrs" as "((% & Hs & _) & (% & Hs2 & _) & Hinstrs)".
         rewrite !ptstomem_to_ptstoSth_2.
         iDestruct "Hs" as "[$ $]".
         rewrite !bv.add_assoc !(@bv.add_comm _ _ s).
         cbn.
         change ([bv [16] 0x1] + [bv 0x1])%bv with [bv [16] 0x2].
         change ([bv [16] 0x2] + [bv 0x1])%bv with [bv [16] 0x3].
         change ([bv [16] 0x3] + [bv 0x1])%bv with [bv [16] 0x4].
         rewrite -bv.add_assoc.
         change ([bv [16] 0x1] + [bv 0x2])%bv with [bv [16] 0x3].
         iDestruct "Hs2" as "[$ $]".
         iApply "IHc".
         by rewrite bv.add_comm.
       - simpl. rewrite !bv.seqBv_succ.
         unfold ptstoSthL. rewrite !big_sepL_cons.
         unfold interp_ptstoinstr.
         iDestruct "Hinstrs" as "((% & Hs & _) & (% & Hs2 & _) & (% & Hs4 & _) & Hinstrs)".
         rewrite !ptstomem_to_ptstoSth_2.
         iDestruct "Hs" as "[$ $]".
         rewrite !bv.add_assoc !(@bv.add_comm _ _ s).
         cbn.
         change ([bv [16] 0x1] + [bv 0x1])%bv with [bv [16] 0x2].
         change ([bv [16] 0x2] + [bv 0x1])%bv with [bv [16] 0x3].
         change ([bv [16] 0x3] + [bv 0x1])%bv with [bv [16] 0x4].
         rewrite -!bv.add_assoc.
         change ([bv [16] 0x1] + [bv 0x2])%bv with [bv [16] 0x3].
         change ([bv [16] 0x1] + [bv 0x4])%bv with [bv [16] 0x5].
         change ([bv [16] 0x4] + [bv 0x1])%bv with [bv [16] 0x5].
         iDestruct "Hs2" as "[$ $]".
         iDestruct "Hs4" as "[$ $]".
         iApply "IHc".
         by rewrite bv.add_comm.
  Qed.
   *)

  Lemma intro_accessible_addresses `{sailGS Σ} :
    ptsto_instrs start_bootcode_start block_start_bootcode ∗
    ptsto_instrs transfer_if_valid_struct_start block_transfer_if_valid_struct ∗
    ptsto_instrs check_struct_start block_check_struct ∗
    ptsto_instrs evaluate_struct_start block_evaluate_struct ∗
    ptsto_instrs mass_erase_start block_mass_erase ∗
    ptstoSthL advAddrs
    ⊢ interp_accessible_addresses segb1 segb2.
  Admitted.


  Lemma evaluate_struct_safe `{sailGS Σ} :
    ⊢
      PC_reg ↦ evaluate_struct_start

      ∗ minimal_pre

      ∗ ipe_register_init

      ∗ R6_reg ↦ (isp_bv + [bv 6])%bv
      ∗ (∃ v, R14_reg ↦ v)
      ∗ R7_reg ↦ MPUIPC0_addr_bv
      ∗ R8_reg ↦ MPUIPSEGB2_addr_bv
      ∗ R9_reg ↦ MPUIPSEGB1_addr_bv
      ∗ R10_reg ↦ saved_ptr_bv
      ∗ R11_reg ↦ valid_flag_bv
      ∗ R12_reg ↦ ipe_sig_valid_src_bv
      ∗ R13_reg ↦ ipe_struct_pointer_src_bv
      ∗ R15_reg ↦ [bv 0xFFFF]
      ∗ registers_not_in_bootcode

      ∗ ptsto_word saved_ptr_bv isp_bv
      ∗ ptsto_word ipe_sig_valid_src_bv valid_flag_bv
      ∗ ptsto_word ipe_struct_pointer_src_bv isp_bv

      ∗ ptsto_word isp_bv ipectl
      ∗ ptsto_word (isp_bv + [bv 2])%bv segb2
      ∗ ptsto_word (isp_bv + [bv 4])%bv segb1
      ∗ (∃ check, ptsto_word (isp_bv + [bv 6])%bv check)

      ∗ inv_fortytwo
      ∗ ptstoSthL advAddrs

      ∗ ptsto_instrs start_bootcode_start block_start_bootcode
      ∗ ptsto_instrs transfer_if_valid_struct_start block_transfer_if_valid_struct
      ∗ ptsto_instrs check_struct_start block_check_struct
      ∗ ptsto_instrs evaluate_struct_start block_evaluate_struct
      ∗ ptsto_instrs mass_erase_start block_mass_erase

      ∗ (PC_reg ↦ (segb1 + [bv 0x8])%bv -∗ WP_loop)

    -∗ WP_loop.
  Proof.
    Local Opaque ptstoSthL ptsto_word.
    iIntros "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28)".
    iApply (evaluate_struct_verified ipectl segb1 segb2 with "[$]").
    iIntros "(H29 & H30 & H31 & H32 & H33 & H34 & H35 & H36 & H37 & H38 & H39 & H40 & H41)".
    iApply fupd_wp.
    iAssert (loop_pre end_addr ipectl segb1 segb2) with "[-]" as "?".
    { iPoseProof (intro_accessible_addresses with "[$H23 $H24 $H25 $H31 $H27 $H22]") as "H42".
      unfold loop_pre, registers_not_in_bootcode.
      iFrame "H30 H32 H33 H34 H42 H8 H9 H10 H11 H12 H35 H36 H37 H38 H28 H4 H13".
      repeat iSplitR; try iLeft; done. }
      (* do 2 iFrame. *)
      (* iSplitR. done. iSplitR. done. iSplitR. iLeft. done. *)
      (* rewrite !ptsto_instrs_extract_ptsto. *)
      (* unfold interp_accessible_addresses, liveAddrs. *)
      (* iSimpl. *)
      (* change (bv.unsigned (bv.of_nat minAddr)) with 0%Z. *)
      (* repeat (unfold bv.of_Z, Z.add, bv.unsigned, Z.of_nat, Nat.add, Pos.succ, Nat.mul, bv.bin, Z.of_N, Pos.add, Pos.mul, Z.mul, Z.shiftl, untrusted, bv.shiftl, bv.of_N, bv.ult, bv.ule, N.lt, N.le, Pos.compare, MSP430IrisInstance.is_mpu_reg_addr; simpl). *)

      (* assert (Gt = Gt <-> True) as -> by done. *)
      (* assert (Lt = Lt <-> True) as -> by done. *)
      (* assert (Gt = Lt <-> False) as -> by done. *)
      (* assert (Lt = Gt <-> False) as -> by done. *)
      (* assert (Gt ≠ Gt <-> False) as -> by done. *)
      (* assert (Lt ≠ Lt <-> False) as -> by done. *)
      (* assert (Lt ≠ Lt <-> True) as -> by done. *)
      (* assert (Gt ≠ Gt <-> True) as -> by done. *)
    iPoseProof (valid_semTriple_loop $! end_addr ipectl segb1 segb2 with "[$]") as "H".
    iModIntro. cbn. unfold semWP.
    iApply (wp_mono with "H"). auto.
  Qed.

  Lemma mass_erase_safe `{sailGS Σ} :
    ⊢ minimal_pre ∗
      PC_reg ↦ mass_erase_start ∗
      ptsto_instrs mass_erase_start block_mass_erase ∗
      ipe_register_init
    -∗ WP_loop.
  Proof.
    iIntros.
    iApply (mass_erase_verified with "[$]").
    iIntros "[? ?]". done.
  Qed.

  Lemma check_struct_safe `{sailGS Σ} :
    ⊢
      minimal_pre

      ∗ PC_reg ↦ check_struct_start

      ∗ ipe_register_init

      ∗ (∃ v, R6_reg ↦ v)
      ∗ (∃ v, R14_reg ↦ v)
      ∗ R7_reg ↦ MPUIPC0_addr_bv
      ∗ R8_reg ↦ MPUIPSEGB2_addr_bv
      ∗ R9_reg ↦ MPUIPSEGB1_addr_bv
      ∗ R10_reg ↦ saved_ptr_bv
      ∗ R11_reg ↦ valid_flag_bv
      ∗ R12_reg ↦ ipe_sig_valid_src_bv
      ∗ R13_reg ↦ ipe_struct_pointer_src_bv
      ∗ R15_reg ↦ [bv 0xFFFF]
      ∗ registers_not_in_bootcode

      ∗ ptsto_word saved_ptr_bv isp_bv
      ∗ ptsto_word ipe_sig_valid_src_bv valid_flag_bv
      ∗ ptsto_word ipe_struct_pointer_src_bv isp_bv

      ∗ ptsto_word isp_bv ipectl
      ∗ ptsto_word (isp_bv + [bv 2])%bv segb2
      ∗ ptsto_word (isp_bv + [bv 4])%bv segb1
      ∗ (∃ check, ptsto_word (isp_bv + [bv 6])%bv check)

      ∗ ptsto_instrs start_bootcode_start block_start_bootcode
      ∗ ptsto_instrs transfer_if_valid_struct_start block_transfer_if_valid_struct
      ∗ ptsto_instrs check_struct_start block_check_struct
      ∗ ptsto_instrs evaluate_struct_start block_evaluate_struct
      ∗ ptsto_instrs mass_erase_start block_mass_erase

      ∗ inv_fortytwo
      ∗ ptstoSthL advAddrs

      ∗ (PC_reg ↦ (segb1 + [bv 0x8])%bv -∗ WP_loop)

    -∗ WP_loop.
  Proof.
    Local Opaque ptstoSthL ptsto_word.
    iIntros "H". do 20 iDestruct "H" as "[? H]". iDestruct "H" as "[[%check ?] H]".
    repeat iDestruct "H" as "[? H]". iDestruct "H" as "?".
    iApply (check_struct_verified ipectl segb1 segb2 check with "[$]").
    iIntros "(? & [? | ?] & H)"; repeat iDestruct "H" as "[? H]"; iDestruct "H" as "?".
    - iApply (evaluate_struct_safe with "[$]").
    - iApply (mass_erase_safe with "[$]").
  Qed.

  Lemma transfer_if_valid_struct_safe `{sailGS Σ} :
    ⊢
      minimal_pre

      ∗ PC_reg ↦ transfer_if_valid_struct_start

      ∗ ipe_register_init

      ∗ (∃ v, R6_reg ↦ v)
      ∗ (∃ v, R14_reg ↦ v)
      ∗ R7_reg ↦ MPUIPC0_addr_bv
      ∗ R8_reg ↦ MPUIPSEGB2_addr_bv
      ∗ R9_reg ↦ MPUIPSEGB1_addr_bv
      ∗ R10_reg ↦ saved_ptr_bv
      ∗ R11_reg ↦ valid_flag_bv
      ∗ R12_reg ↦ ipe_sig_valid_src_bv
      ∗ R13_reg ↦ ipe_struct_pointer_src_bv
      ∗ R15_reg ↦ [bv 0xFFFF]
      ∗ registers_not_in_bootcode

      ∗ ptsto_word saved_ptr_bv [bv 0]
      ∗ ptsto_word ipe_sig_valid_src_bv valid_flag_bv
      ∗ ptsto_word ipe_struct_pointer_src_bv isp_bv

      ∗ ptsto_word isp_bv ipectl
      ∗ ptsto_word (isp_bv + [bv 2])%bv segb2
      ∗ ptsto_word (isp_bv + [bv 4])%bv segb1
      ∗ (∃ check, ptsto_word (isp_bv + [bv 6])%bv check)

      ∗ ptsto_instrs start_bootcode_start block_start_bootcode
      ∗ ptsto_instrs transfer_if_valid_struct_start block_transfer_if_valid_struct
      ∗ ptsto_instrs check_struct_start block_check_struct
      ∗ ptsto_instrs evaluate_struct_start block_evaluate_struct
      ∗ ptsto_instrs mass_erase_start block_mass_erase

      ∗ inv_fortytwo
      ∗ ptstoSthL advAddrs

      ∗ (PC_reg ↦ (segb1 + [bv 0x8])%bv -∗ WP_loop)

    -∗ WP_loop.
  Proof.
    Local Opaque ptstoSthL ptsto_word.
    iIntros "(H & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27)".
    iApply (transfer_if_valid_struct_verified with "[$]").
    iIntros "(H38 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & H35 & H36 & H37)".
    iApply (check_struct_safe with "[$H38 $H28 $H30 $H2 $H3 $H4 $H5 $H6 $H31 $H32 $H33 $H34 $H11 $H12 $H37 $H35 $H36 $H16 $H17 $H18 $H19 $H20 $H29 $H22 $H23 $H24 $H25 $H26 $H27]").
  Qed.

  Lemma start_bootcode_safe `{sailGS Σ} :
    ⊢
      minimal_pre

      ∗ PC_reg ↦ start_bootcode_start

      ∗ ipe_register_init

      ∗ (∃ v, R6_reg ↦ v)
      ∗ (∃ v, R14_reg ↦ v)
      ∗ R7_reg ↦ MPUIPC0_addr_bv
      ∗ R8_reg ↦ MPUIPSEGB2_addr_bv
      ∗ R9_reg ↦ MPUIPSEGB1_addr_bv
      ∗ R10_reg ↦ saved_ptr_bv
      ∗ R11_reg ↦ valid_flag_bv
      ∗ R12_reg ↦ ipe_sig_valid_src_bv
      ∗ R13_reg ↦ ipe_struct_pointer_src_bv
      ∗ R15_reg ↦ [bv 0xFFFF]
      ∗ registers_not_in_bootcode

      ∗ (ptsto_word saved_ptr_bv [bv 0]
         ∨ ptsto_word saved_ptr_bv isp_bv)
      ∗ ptsto_word ipe_sig_valid_src_bv valid_flag_bv
      ∗ ptsto_word ipe_struct_pointer_src_bv isp_bv

      ∗ ptsto_word isp_bv ipectl
      ∗ ptsto_word (isp_bv + [bv 2])%bv segb2
      ∗ ptsto_word (isp_bv + [bv 4])%bv segb1
      ∗ (∃ check, ptsto_word (isp_bv + [bv 6])%bv check)

      ∗ ptsto_instrs start_bootcode_start block_start_bootcode
      ∗ ptsto_instrs transfer_if_valid_struct_start block_transfer_if_valid_struct
      ∗ ptsto_instrs check_struct_start block_check_struct
      ∗ ptsto_instrs evaluate_struct_start block_evaluate_struct
      ∗ ptsto_instrs mass_erase_start block_mass_erase

      ∗ inv_fortytwo
      ∗ ptstoSthL advAddrs

      ∗ (PC_reg ↦ (segb1 + [bv 0x8])%bv -∗ WP_loop)

    -∗ WP_loop.
  Proof.
    Local Opaque ptstoSthL ptsto_word.
    iIntros "(H33 & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27)".
    iApply (start_bootcode_verified with "[$]").
    iIntros "(H34 & H28 & H29 & H30 & [[H31 H32] | [H31 H32]])".
    - iApply (transfer_if_valid_struct_safe with "[$H34 $H32 $H28 $H2 $H3 $H4 $H5 $H6 $H30 $H8 $H9 $H10 $H11 $H12 $H31 $H14 $H15 $H16 $H17 $H18 $H19 $H29 $H21 $H22 $H23 $H24 $H25 $H26 $H27]").
    - iApply (check_struct_safe with "[$H34 $H32 $H28 $H2 $H3 $H4 $H5 $H6 $H30 $H8 $H9 $H10 $H11 $H12 $H31 $H14 $H15 $H16 $H17 $H18 $H19 $H29 $H21 $H22 $H23 $H24 $H25 $H26 $H27]").
  Qed.

  Lemma intro_ptsto_word `{sailGS Σ} v0 v1 (a : bv 16) :
    interp_ptsto (bv.of_Z (0 + bv.unsigned a)) v0 ∗
    interp_ptsto (bv.of_Z (1 + bv.unsigned a)) v1
    ⊢ ptsto_word a (bv.app v0 v1).
  Proof.
    iIntros "(Hmema & Hmema1)".
    Local Transparent ptsto_word.
    unfold ptsto_word, interp_ptstomem.
    rewrite ?bv.appView_app.
    replace (@bv.of_Z 16 (0 + bv.unsigned a)%Z) with a by now rewrite bv.of_Z_unsigned.
    replace (@bv.of_Z 16 (1 + bv.unsigned a)%Z) with (bv.add bv.one a) by now rewrite <-bv.of_Z_add, bv.of_Z_unsigned.
    replace v1 with (bv.app v1 bv.nil) by now rewrite (bv.app_nil_r v1).
    rewrite ?bv.appView_app. rewrite (bv.app_nil_r v1). simpl.
    now iFrame.
  Qed.

  Lemma intro_ptsto_word2 `{sailGS Σ} {μ : Memory} {a v : bv 16} :
    mem_has_word μ a v ->
    ([∗ list] a' ∈ bv.seqBv a 2, interp_ptsto a' (μ a')) ⊢ ptsto_word a v.
  Proof.
    iIntros (Hmhw) "Hmem".
    destruct Hmhw as (v0 & v1 & Heqμ & Heqv).
    unfold bv.seqBv, seqZ. change (seq 0 ?x) with [0;1]%list%nat.
    cbn -[bv.add interp_ptstomem].
    iDestruct "Hmem" as "(Hmema & Hmema1 & _)".
    inversion Heqμ; subst.
    now iApply (intro_ptsto_word with "[$Hmema $Hmema1]").
  Qed.

  Lemma intro_ptstoSthL `{sailGS Σ} (μ : Memory) (addrs : list (bv 16))  :
    ([∗ list] a' ∈ addrs, interp_ptsto a' (μ a')) ⊢ ptstoSthL addrs.
  Proof.
    Local Transparent ptstoSthL.
    induction addrs as [|a l]; cbn.
    - now iIntros "_".
    - iIntros "[Hmema Hmem]".
      iSplitL "Hmema".
      + now iExists (μ a).
      + now iApply IHl.
  Qed.

  Lemma intro_ptstoinstr_I `{sailGS Σ} {μ : Memory} {a : bv 16} {instr : ast} :
    (2 + bv.bin a < bv.exp2 16)%N ->
    mem_has_instr μ a instr ->
    ([∗ list] a' ∈ bv.seqBv a 2, interp_ptsto a' (μ a'))
      ⊢ interp_ptstoinstr a (Base.I instr).
  Proof.
    iIntros (Hrep (v & Hmhw & Heq)) "Hmem".
    iExists v.
    iSplitL; first iApply intro_ptsto_word2; done.
  Qed.

  Lemma intro_ptstoinstr_D `{sailGS Σ} {μ : Memory} {a : bv 16} {data} :
    (2 + bv.bin a < bv.exp2 16)%N ->
    mem_has_word μ a data ->
    ([∗ list] a' ∈ bv.seqBv a 2, interp_ptsto a' (μ a'))
      ⊢ interp_ptstoinstr a (Base.D data).
  Proof.
    iIntros.
    iExists data.
    iSplitL; first iApply (intro_ptsto_word2 (μ := μ)); auto.
  Qed.

  Lemma intro_ptsto_instrs `{sailGS Σ} {μ : Memory} {a : bv 16} {instrs : list ast_with_args} :
    (N.of_nat (code_size instrs) + bv.bin a < bv.exp2 16)%N ->
    mem_has_instrs μ a instrs ->
    ([∗ list] a' ∈ bv.seqBv a (code_size instrs), interp_ptsto a' (μ a'))
      ⊢ ptsto_instrs a instrs.
  Proof.
    iIntros (Hrep Hmeminstrs) "Hmem".
    iInduction instrs as [|instr instrs] "IH" forall (a Hrep Hmeminstrs).
    - done.
    - rewrite Nat2N.inj_succ in Hrep.
      destruct instr;
        simpl (code_size (_ :: instrs));
        [ replace (S (S (code_size instrs))) with (2 + code_size instrs)%nat by lia
        | replace (S (S (S (S (code_size instrs))))) with (4 + code_size instrs)%nat by lia
        | replace (S (S (S (S (S (S (code_size instrs))))))) with (6 + code_size instrs)%nat by lia ];
        rewrite bv.seqBv_app big_opL_app;
        [ destruct Hmeminstrs as [Hinstr Hmeminstrs]
        | destruct Hmeminstrs as [Hinstr [Hdata Hmeminstrs]]
        | destruct Hmeminstrs as [Hinstr [Hdata0 [Hdada1 Hmeminstrs]]]];
        iDestruct "Hmem" as "[Hmema Hmema2]".
      + assert (N.of_nat (code_size (I0 i :: instrs)) >= 2)%N by (simpl; lia).
        iSplitL "Hmema".
        * iApply (intro_ptstoinstr_I with "Hmema"); auto. lia.
        * iApply ("IH" with "[%] [% //] [-]").
          -- rewrite bv.bin_add_small;
               cbn -[N.mul] in *;
               now Lia.lia.
          -- now rewrite ?bv.add_assoc.
      + assert (N.of_nat (code_size (I1 i a0 :: instrs)) >= 4)%N by (simpl; lia).
        change 4%nat with (2 + 2)%nat at 7.
        rewrite bv.seqBv_app big_sepL_app.
        iDestruct "Hmema" as "[HmemI HmemD]".
        iSplitL "HmemI".
        * iApply (intro_ptstoinstr_I (μ := μ)); auto. lia.
        * iSplitL "HmemD".
          -- iApply (intro_ptstoinstr_D (μ := μ)); auto.
             rewrite bv.bin_add. simpl.
             assert (2 + (bv.bin a + 2) `mod` bv.exp2 16 <= 2 + (bv.bin a + 2))%N.
             { apply N.add_le_mono_l. apply N.Div0.mod_le. }
             lia.
          -- iApply ("IH" with "[%] [% //] [-]").
             ++ rewrite bv.bin_add_small;
                  cbn -[N.mul] in *;
                  now Lia.lia.
             ++ now rewrite ?bv.add_assoc.
      + assert (N.of_nat (code_size (I2 i a0 b :: instrs)) >= 6)%N by (simpl; lia).
        change 6%nat with (2 + 2 + 2)%nat at 7.
        rewrite !bv.seqBv_app !big_sepL_app.
        iDestruct "Hmema" as "[[HmemI HmemD0] HmemD1]".
        iSplitL "HmemI".
        * iApply (intro_ptstoinstr_I (μ := μ)); auto. lia.
        * iSplitL "HmemD0".
          -- iApply (intro_ptstoinstr_D (μ := μ)); auto.
             rewrite bv.bin_add. simpl.
             assert (2 + (bv.bin a + 2) `mod` bv.exp2 16 <= 2 + (bv.bin a + 2))%N.
             { apply N.add_le_mono_l. apply N.Div0.mod_le. }
             lia.
          -- iSplitL "HmemD1".
             ++ iApply (intro_ptstoinstr_D (μ := μ)); auto.
                rewrite bv.bin_add. simpl.
                assert (2 + (bv.bin a + 4) `mod` bv.exp2 16 <= 2 + (bv.bin a + 4))%N.
                { apply N.add_le_mono_l. apply N.Div0.mod_le. }
                lia.
             ++ iApply ("IH" with "[%] [% //] [-]").
                ** rewrite bv.bin_add_small;
                     cbn -[N.mul] in *;
                     now Lia.lia.
                ** now rewrite ?bv.add_assoc.
  Qed.

  Lemma in_seqBv_bounds : forall (s : bv 16) (l : nat) (y : bv 16),
      (bv.unsigned s + l < 2 ^ 16)%Z ->
      y ∈ bv.seqBv s l ->
      (s <=ᵘ y /\ y <ᵘ bv.add s (bv.of_nat l))%bv.
  Proof.
    intros s l y Hrep Hy.
    unfold bv.seqBv in Hy.
    apply list.elem_of_list_fmap in Hy.
    destruct Hy as [y' [-> Hy']].
    apply elem_of_seqZ in Hy'.
    pose proof (bv.unsigned_bounds s) as H_s_bounds.
    split.
    - destruct Hy' as [Hlo Hhi].
      apply bv.ule_iff_unsigned_le.
      rewrite bv.unsigned_of_Z.
      unfold bv.truncz.
      rewrite Zmod_small.
      assumption. lia.
    - destruct Hy' as [Hlo Hhi].
      apply bv.ult_iff_unsigned_lt.
      rewrite bv.unsigned_of_Z.
      unfold bv.truncz.
      rewrite Zmod_small; last lia.
      replace (bv.unsigned (s + bv.of_nat l)) with (bv.unsigned s + l)%Z;
        first assumption.
      apply (Z.le_lt_add_lt 0 l (bv.unsigned s) (2 ^ 16)) in Hrep as Hsrep; [|lia].
      rewrite bv.unsigned_add.
      assert (@bv.unsigned 16 (bv.of_nat l) = l) as ->.
      { unfold bv.unsigned.
        rewrite bv.bin_of_nat_small.
        { apply nat_N_Z. }
        rewrite Z.add_comm in Hrep.
        apply (Z.le_lt_add_lt 0 (bv.unsigned s) l (2 ^ 16))
          in Hrep as Hlrep; lia. }
      unfold bv.truncz.
      rewrite Zmod_small; lia.
  Qed.

  Lemma sub_heap_mapsto_interp_ptsto {Σ : gFunctors} {H : sailGS Σ} {s : bv 16} {e : nat} (μ : Memory):
    (N.of_nat minAddr <= bv.bin s /\ bv.bin s + (N.of_nat e) <= N.of_nat (minAddr + lenAddr)
     \/ 0x4200 <= bv.bin s /\ bv.bin s + (N.of_nat e) <= 0x420A
     \/ 0xFF88 <= bv.bin s /\ bv.bin s + (N.of_nat e) <= 0xFF8C)%N
    ->
    ([∗ list] y ∈ bv.seqBv s e, gen_heap.pointsto y (dfrac.DfracOwn 1) (μ y))
      ⊢ [∗ list] a' ∈ bv.seqBv s e, interp_ptsto a' (μ a').
  Proof.
    iIntros ([[Hlo Hhi] | [[Hlo Hhi] | [Hlo Hhi]]]) "Hlist";
    iApply (big_sepL_mono with "Hlist"); intros ? ? Hsom; cbn;
    iIntros "$"; iPureIntro;
    apply elem_of_list_lookup_2 in Hsom;
    unfold MSP430IrisInstance.is_mpu_reg_addr; intro;
    unfold minAddr, lenAddr in *; cbn in Hhi;
    apply in_seqBv_bounds in Hsom.
    - assert (bv.ult [bv [16] 0x5a0] (bv.of_nat 200))%bv by solve_bv.
      by compute in H1.
    - solve_bv.
    - assert (bv.ule (bv.of_N 16896) s)%bv by solve_bv.
      assert (bv.ule (bv.of_N 16896) [bv [16] 0x5b0])%bv by solve_bv.
      by compute in H2.
    - solve_bv.
    - assert (bv.ule (bv.of_N 65416) s)%bv by solve_bv.
      assert (bv.ule (bv.of_N 65416) [bv [16] 0x5b0])%bv by solve_bv.
      by compute in H2.
    - solve_bv.
Qed.

  Lemma liveAddrs_split :
    liveAddrs =
      (bv.seqBv start_bootcode_start start_bootcode_size
      ++ bv.seqBv transfer_if_valid_struct_start transfer_if_valid_struct_size
      ++ bv.seqBv check_struct_start check_struct_size
      ++ bv.seqBv evaluate_struct_start evaluate_struct_size
      ++ bv.seqBv mass_erase_start mass_erase_size
      ++ advAddrs1
      ++ bv.seqBv (bv.shiftl segb1 [bv [3] 4]) (Z.to_nat (bv.unsigned data_addr - bv.unsigned segb1 * 16))
      ++ [data_addr]
      ++ bv.seqBv (data_addr + [bv 1]) (Z.to_nat (bv.unsigned segb2 * 16 - bv.unsigned data_addr - 1))
      ++ advAddrs2
      ++ bv.seqBv saved_ptr_bv 2
      ++ bv.seqBv isp_bv 2
      ++ bv.seqBv (isp_bv + [bv 2]) 2
      ++ bv.seqBv (isp_bv + [bv 4]) 2
      ++ bv.seqBv (isp_bv + [bv 6]) 2
      ++ bv.seqBv ipe_sig_valid_src_bv 2
      ++ bv.seqBv ipe_struct_pointer_src_bv 2)%list.
  Proof. now compute. Qed.

  Lemma bootcode_splitMemory `{sailGS Σ} {μ : Memory} :
    mem_has_instrs μ start_bootcode_start block_start_bootcode ->
    mem_has_instrs μ transfer_if_valid_struct_start block_transfer_if_valid_struct ->
    mem_has_instrs μ check_struct_start block_check_struct ->
    mem_has_instrs μ evaluate_struct_start block_evaluate_struct ->
    mem_has_instrs μ mass_erase_start block_mass_erase ->

    (mem_has_word μ saved_ptr_bv [bv 0]
     \/ mem_has_word μ saved_ptr_bv isp_bv) ->
    mem_has_word μ ipe_sig_valid_src_bv valid_flag_bv ->
    mem_has_word μ ipe_struct_pointer_src_bv isp_bv ->

    mem_has_word μ isp_bv ipectl ->
    mem_has_word μ (isp_bv + [bv 2])%bv segb2 ->
    mem_has_word μ (isp_bv + [bv 4])%bv segb1 ->

    μ data_addr = [bv 42] ->

    @mem_res _ sailGS_memGS μ ⊢
      |={⊤}=>
          ptsto_instrs start_bootcode_start block_start_bootcode ∗
          ptsto_instrs transfer_if_valid_struct_start block_transfer_if_valid_struct ∗
          ptsto_instrs check_struct_start block_check_struct ∗
          ptsto_instrs evaluate_struct_start block_evaluate_struct ∗
          ptsto_instrs mass_erase_start block_mass_erase ∗

          (ptsto_word saved_ptr_bv [bv 0] ∨ ptsto_word saved_ptr_bv isp_bv) ∗
          ptsto_word ipe_sig_valid_src_bv valid_flag_bv ∗
          ptsto_word ipe_struct_pointer_src_bv isp_bv ∗

          ptsto_word isp_bv ipectl ∗
          ptsto_word (isp_bv + [bv 2])%bv segb2 ∗
          ptsto_word (isp_bv + [bv 4])%bv segb1 ∗
          (∃ check, ptsto_word (isp_bv + [bv 6])%bv check) ∗

          inv_fortytwo ∗
          ptstoSthL advAddrs.
  Proof.
    iIntros (μstart μtransfer μcheck μeval μerase
               μsaved μvalid μisp μipectl μsegb2 μsegb1 μft) "Hmem".
    unfold mem_res, initMemMap.
    rewrite liveAddrs_split.
    rewrite ?map_app ?list_to_map_app ?big_sepM_union.
    iDestruct "Hmem" as "(Hstart & Htransfer & Hcheck & Heval & Herase
                           & Hadv1 & Hipe1 & Hft & Hipe2 & Hadv2 & Hsaved
                           & Hipectl & Hsegb2 & Hsegb1 & Hcksum
                           & Hvalid & Hisp)".
    iSplitL "Hstart".
    { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Hstart"); compute; by left. }
    iSplitL "Htransfer".
    { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Htransfer"); compute; by left. }
    iSplitL "Hcheck".
    { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Hcheck"); compute; by left. }
    iSplitL "Heval".
    { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Heval"); compute; by left. }
    iSplitL "Herase".
    { iApply (intro_ptsto_instrs (μ := μ)); [easy..|].
      iApply (sub_heap_mapsto_interp_ptsto with "Herase"); compute; by left. }
    iSplitL "Hsaved".
    { destruct μsaved as [μsaved | μsaved];
        [iLeft | iRight];
        iApply (intro_ptsto_word2 μsaved);
        iApply (sub_heap_mapsto_interp_ptsto with "Hsaved");
        compute; right; by left. }
    iSplitL "Hvalid".
    { iApply (intro_ptsto_word2 μvalid).
      iApply (sub_heap_mapsto_interp_ptsto with "Hvalid");
        compute. right; by right. }
    iSplitL "Hisp".
    { iApply (intro_ptsto_word2 μisp).
      iApply (sub_heap_mapsto_interp_ptsto with "Hisp");
        compute; right; by right. }
    iSplitL "Hipectl".
    { iApply (intro_ptsto_word2 μipectl).
      iApply (sub_heap_mapsto_interp_ptsto with "Hipectl");
        compute; right; by left. }
    iSplitL "Hsegb2".
    { iApply (intro_ptsto_word2 μsegb2).
      iApply (sub_heap_mapsto_interp_ptsto with "Hsegb2");
        compute; right; by left. }
    iSplitL "Hsegb1".
    { iApply (intro_ptsto_word2 μsegb1).
      iApply (sub_heap_mapsto_interp_ptsto with "Hsegb1");
        compute; right; by left. }
    iSplitL "Hcksum".
    { iExists (bv.app (μ (isp_bv + [bv 6])) (μ (isp_bv + [bv 7])))%bv.
      assert (mem_has_word μ (isp_bv + [bv 6])
                (bv.app (μ (isp_bv + [bv 6])) (μ (isp_bv + [bv 7]))))%bv
        as μcksum
        by now (exists (μ (isp_bv + [bv 0x6])%bv);
                exists (μ (isp_bv + [bv 0x7])%bv)).
      iApply (intro_ptsto_word2 μcksum).
      iApply (sub_heap_mapsto_interp_ptsto with "Hcksum");
         compute; right; by left. }
    iSplitL "Hft".
    {
      iAssert (interp_ptsto data_addr [bv 42]) with "[Hft]" as "Hft".
      { unfold interp_ptsto. simpl.
        rewrite μft. iDestruct "Hft" as "[Hft _]".
        iFrame. iPureIntro. now compute. }
      iMod (inv.inv_alloc boot_inv_ro_ns ⊤ (interp_ptsto data_addr [bv 42]) with "Hft")
        as "Hinv".
      now iModIntro.
    }
    iApply (intro_ptstoSthL μ).
    iApply big_sepL_app.
    iSplitL "Hadv1".
    - iApply (sub_heap_mapsto_interp_ptsto with "Hadv1"); compute; by left.
    - iApply (sub_heap_mapsto_interp_ptsto with "Hadv2"); compute; by left.
  Qed.

  Lemma interp_ptsto_valid `{sailGS Σ} {μ a v} :
    ⊢ mem_inv _ μ -∗ interp_ptsto a v -∗ ⌜μ a = v⌝.
  Proof.
    unfold interp_ptsto, mem_inv.
    iIntros "(%memmap & Hinv & %link) [Hptsto %Hmpu]".
    iDestruct (gen_heap.gen_heap_valid with "Hinv Hptsto") as "%x".
    iPureIntro.
    now apply (map_Forall_lookup_1 _ _ _ _ link).
  Qed.

  Lemma bv0_is_nil (x : bv 0) : x = bv.nil.
  Proof.
    destruct x as [bin wf].
    destruct bin; first by apply bv.bin_inj.
    by exfalso.
  Qed.

  (*
  Lemma interp_ptstomem_valid `{sailGS Σ} {μ} {a v : bv 16} :
    ⊢ mem_inv _ μ -∗ @interp_ptstomem _ _ 2 a v -∗ ⌜mem_has_word μ a v⌝.
  Proof.
    iIntros "Hinv Hptstomem".
    destruct (bv.appView 8 8 v) as [v1 v2].
    destruct (bv.appView 8 0 v2) as [v2 ?].
    repeat iExists _.
    iSplit; last eauto.
    rewrite !ptstomem_bv_app.
    iDestruct "Hptstomem" as "(Ha0 & Ha1 & Htail)".
    iDestruct (interp_ptsto_valid with "Hinv Ha0") as "%Hm0".
    iDestruct (interp_ptsto_valid with "Hinv Ha1") as "%Hm1".
    iPureIntro.
    rewrite (bv0_is_nil ys) bv.app_nil_r.
    rewrite !bv.seqBv_succ !map_cons.
    repeat f_equal; auto.
  Qed.
   *)

  Lemma bootcode_endToEnd
    {γ γ' : RegStore} {μ μ' : Memory} {δ δ' : CStore [ctx]} {s' : Stm [ctx] ty.unit} :

    (* TODO require whole machine state
     doesn't make much sense as we don't have chunks for protected addrs
     maybe require ipe configuration? *)
    (forall `{sailGS Σ}, ⊢ (PC_reg ↦ (segb1 + [bv 0x8])%bv -∗ WP_loop) : iProp Σ) ->

    mem_has_instrs μ start_bootcode_start block_start_bootcode ->
    mem_has_instrs μ transfer_if_valid_struct_start block_transfer_if_valid_struct ->
    mem_has_instrs μ check_struct_start block_check_struct ->
    mem_has_instrs μ evaluate_struct_start block_evaluate_struct ->
    mem_has_instrs μ mass_erase_start block_mass_erase ->

    (mem_has_word μ saved_ptr_bv [bv 0]
     \/ mem_has_word μ saved_ptr_bv isp_bv) ->
    mem_has_word μ ipe_sig_valid_src_bv valid_flag_bv ->
    mem_has_word μ ipe_struct_pointer_src_bv isp_bv ->

    mem_has_word μ isp_bv ipectl ->
    mem_has_word μ (isp_bv + [bv 2])%bv segb2 ->
    mem_has_word μ (isp_bv + [bv 4])%bv segb1 ->

    read_register γ PC_reg = start_bootcode_start ->
    read_register γ MPUIPC0_reg = [bv 0] ->

    (* work around unsupported immediate/absolute addressing *)
    read_register γ R7_reg = MPUIPC0_addr_bv ->
    read_register γ R8_reg = MPUIPSEGB2_addr_bv ->
    read_register γ R9_reg = MPUIPSEGB1_addr_bv ->
    read_register γ R10_reg = saved_ptr_bv ->
    read_register γ R11_reg = valid_flag_bv ->
    read_register γ R12_reg = ipe_sig_valid_src_bv ->
    read_register γ R13_reg = ipe_struct_pointer_src_bv ->
    read_register γ R15_reg = [bv 0xFFFF] ->

    μ data_addr = [bv 42] ->

    ⟨ γ, μ, δ, fun_loop ⟩ --->* ⟨ γ', μ', δ', s' ⟩ ->

    μ' data_addr = [bv 42].
  Proof.
    intros
      Htrusted_safe
      μstart μtransfer μcheck μeval μerase
      μsaved μvalid μisp
      μipectl μsegb1 μsegb2
      γpc γipectl
      γr7 γr8 γr9 γr10 γr11 γr12 γr13 γr15
      μft
      steps.
    refine (adequacy_gen (Q := fun _ _ _ _ => True%I) _ steps _).
    iIntros (Σ ?).
    unfold own_regstore.
    cbn.
    iIntros "(Hmem & H')".
    rewrite γpc γipectl γr7 γr8 γr9 γr10 γr11 γr12 γr13 γr15.
    iMod (bootcode_splitMemory with "Hmem")
      as "(Hstart & Htransfer & Hcheck & Heval & Herase
           & Hsaved & Hvalid & Hisp & Hipectl & Hsegb2 & segb1 & Hchksum & #Hft & Hadv)";
      try assumption.
    iModIntro.
    iSplitR "".
    - destruct (env.view δ).
      repeat (iDestruct "H'" as "[? H']").
      iPoseProof (start_bootcode_safe with "[-]") as "H".
      { Local Opaque ptsto_instrs.
        iPoseProof Htrusted_safe as "Htrusted_safe".
        iFrame "∗ #". }
      iApply (semWP_mono with "H"). by iIntros ([] _) "_".
    - iIntros "Hmem".
      iInv "Hft" as ">Hptsto" "_".
      iDestruct (interp_ptsto_valid with "Hmem Hptsto") as "$".
      iApply fupd_mask_intro; first set_solver.
      now iIntros "_".
  Qed.
End Bootcode.
