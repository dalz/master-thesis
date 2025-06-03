From Coq Require Import
     ZArith.ZArith
     Lists.List
     micromega.Lia
     Strings.String.
From Katamaran Require Import
     Notations
     Bitvector
     Semantics.

From MSP430 Require Import
  BlockVer.Spec
  BlockVer.Verifier
  Machine
  Sig.

Import MSP430Program.
Import MSP430BlockVerifExecutor.
Import Assembly.

Set Implicit Arguments.
Import ctx.resolution.
Import ctx.notations.
Import bv.notations.
Import env.notations.
Import ListNotations.
Import asn.notations.
Import Erasure.notations.

Module Examples.
  Import Utils.

  Definition asn_ipe_registers_zero {Σ} : Assertion Σ :=
      MPUIPC0_reg    ↦ term_val ty.wordBits [bv 0]
    ∗ MPUIPSEGB1_reg ↦ term_val ty.wordBits [bv 0]
    ∗ MPUIPSEGB2_reg ↦ term_val ty.wordBits [bv 0].

  Definition minimal_pre {Σ} (include_ipe : bool) : Assertion Σ :=
      ∃ "lif", LastInstructionFetch ↦ term_var "lif"
    ∗ ∃ "srcg1", SRCG1_reg ↦ term_var "srcg1"
    ∗ (* if include_ipe then asn_ipe_registers else *) ⊤
    ∗ asn_mpu_registers.

  Definition minimal_post {Σ} (include_ipe : bool) : Assertion Σ :=
    minimal_pre include_ipe.

  Record BlockVerifierContract {Σ} :=
    MkBlockVerifierContract
      { precondition  : Assertion (Σ ▻ "a" :: ty.Address)
      ; instrs        : list ast_with_args
      ; postcondition : Assertion (Σ ▻ "a" :: ty.Address ▻ "an" :: ty.Address)
      }.

  Definition MkValidBlockVerifierContract {Σ} (include_ipe : bool) (c : @BlockVerifierContract Σ) : Prop :=
  match c with
    {| precondition := pre; instrs := i; postcondition := post |} =>
      safeE (* VerificationCondition *) (postprocess
               (sblock_verification_condition
                  (minimal_pre include_ipe ∗ pre)
                  i
                  (minimal_post include_ipe ∗ post)
                  wnil))
  end.

  Definition ValidBlockVerifierContract {Σ} := @MkValidBlockVerifierContract Σ true.
  Definition ValidBlockVerifierContractWithExplicitIPE {Σ} := @MkValidBlockVerifierContract Σ false.

  Local Notation "'{{' P '}}' i '{{' Q '}}'" :=
    (@MkBlockVerifierContract [ctx] P%asn i Q%asn)
      (at level 90, format "'[v' '{{'  P  '}}' '/'  i '/' '{{'  Q  '}}' ']'").
  Local Notation "'{{' P '}}' i '{{' Q '}}' 'with' logvars" :=
    (@MkBlockVerifierContract logvars P%asn i Q%asn)
      (at level 90, format "'[v' '{{'  P  '}}' '/'  i '/' '{{'  Q  '}}' '/' 'with'  logvars ']'").

  Local Ltac solve_bv :=
      repeat match goal with
        | |- context[bv.add ?x (@bv.mk ?n 0 I)] =>
            fold (@bv.zero n)
        | |- context[bv.add ?x bv.zero] =>
            rewrite bv.add_zero_r
        end.

  Local Ltac symbolic_simpl :=
    vm_compute; constructor; simpl.

  Definition asn_init_pc {Σ} (pc : Term _ ty.Address) : Assertion (Σ ▻ "a" :: ty.Address) :=
    term_var "a" = pc.
  Definition asn_fin_pc {Σ} (pc : Term _ ty.Address) : Assertion (Σ ▻ "an" :: ty.Address) :=
    term_var "an" = pc.

  Definition ex_mov_register : BlockVerifierContract :=
    {{
        asn_init_pc (term_val ty.Address [bv 0]) ∗
        asn_ipe_registers_zero ∗
        R4_reg ↦ term_val ty.wordBits [bv 42] ∗
        ∃ "v", R5_reg ↦ term_var "v"
    }}

    [mov_rr R4 R5]

    {{
        asn_ipe_registers_zero ∗
        R4_reg ↦ term_val ty.wordBits [bv 42] ∗
        R5_reg ↦ term_val ty.wordBits [bv 42]
    }}.


  Example valid_ex_move_register : ValidBlockVerifierContract ex_mov_register.
  Proof. now symbolic_simpl. Qed.


(* { valid sig \/ saved }
   bootcode
   { ipe initialized with struct \/ erase } *)

  Section Bootcode.
    Local Notation "v -' n" :=
      (term_binop bop.bvsub v (term_val ty.wordBits [bv n]))
      (at level 50).

    Definition asn_byte_zero {Σ} (b : Term Σ ty.byteBits) : Assertion Σ :=
      b = term_val ty.byteBits [bv 0].

    Definition saved_ptr_loc {Σ} : Term Σ _ := term_val ty.Address [bv 0x4200].
    Definition saved_ptr {Σ} : Term Σ _ := term_val ty.Address [bv 0x4202].
    Definition conf_ipectl {Σ} : Term Σ _ := term_val ty.Address [bv 0x00CD].
    Definition conf_segb1 {Σ} : Term Σ _ := term_val ty.Address [bv 0x6000].
    Definition conf_segb2 {Σ} : Term Σ _ := term_val ty.Address [bv 0x6100].

    Definition byte_zero {Σ} : Term Σ _ := term_val ty.byteBits [bv 0].

    Definition valid_flag {Σ} : Term Σ _ := term_val ty.wordBits [bv 0xAAAA].
    Definition ipe_sig_valid_src {Σ} : Term Σ _ := term_val ty.Address [bv 0xFF88].
    Definition ipe_struct_pointer_src {Σ} : Term Σ _ := term_val ty.Address [bv 0xFF8A].

    Definition start_bootcode_start{Σ} : Term Σ _ := term_val ty.wordBits [bv 0].
    Definition transfer_if_valid_struct_start {Σ} : Term Σ _ := term_val ty.wordBits [bv 0x4].
    Definition check_struct_start {Σ} : Term Σ _ := term_val ty.wordBits [bv 0xC].
    Definition evaluate_struct_start {Σ} : Term Σ _ := term_val ty.wordBits [bv 0x20].
    Definition mass_erase_start {Σ} : Term Σ _ := term_val ty.wordBits [bv 0x2A].
    Definition end_addr {Σ} : Term Σ _ := term_val ty.wordBits [bv 0x38].

    Definition asn_flag_valid {Σ} : Assertion Σ :=
      asn_ptsto_word ipe_sig_valid_src (low valid_flag) (high valid_flag).

    Definition asn_conf {Σ} : Assertion Σ :=
        saved_ptr      m↦ low  conf_ipectl
      ∗ saved_ptr +' 1 m↦ high conf_ipectl
      ∗ saved_ptr +' 2 m↦ low  conf_segb2
      ∗ saved_ptr +' 3 m↦ high conf_segb2
      ∗ saved_ptr +' 4 m↦ low  conf_segb1
      ∗ saved_ptr +' 5 m↦ high conf_segb1.

    Definition contract_start_bootcode : BlockVerifierContract :=
      {{
            asn_init_pc start_bootcode_start
          ∗ asn_ipe_registers_zero

          ∗ R10_reg ↦ saved_ptr_loc
          ∗ (asn_ptsto_word saved_ptr_loc byte_zero byte_zero
             ∨ asn_ptsto_word saved_ptr_loc (low saved_ptr) (high saved_ptr))
      }}
        [ tst_m R10
        ; jnz [bv 4] (* check_struct *)]
      {{
            R10_reg ↦ saved_ptr_loc
          ∗ asn_ipe_registers_zero
          ∗ ( asn_ptsto_word saved_ptr_loc byte_zero byte_zero
                ∗ asn_fin_pc transfer_if_valid_struct_start
              ∨ asn_ptsto_word saved_ptr_loc (low saved_ptr) (high saved_ptr)
                ∗ asn_fin_pc check_struct_start)
      }}.

    Definition contract_transfer_if_valid_struct : BlockVerifierContract :=
      {{
            asn_init_pc transfer_if_valid_struct_start

          ∗ asn_ipe_registers_zero
          ∗ R10_reg ↦ saved_ptr_loc
          ∗ R11_reg ↦ valid_flag
          ∗ R12_reg ↦ ipe_sig_valid_src
          ∗ R13_reg ↦ ipe_struct_pointer_src

          ∗ asn_flag_valid
          ∗ asn_ptsto_word ipe_struct_pointer_src (low saved_ptr) (high saved_ptr)
          ∗ asn_ptsto_word saved_ptr_loc byte_zero byte_zero
      }}
        [ cmp_rm R11 R12
        ; jnz [bv 0x34] (* TODO end *)
        ; mov_mm R13 R10 ]
      {{
            asn_fin_pc check_struct_start

          ∗ asn_ipe_registers_zero
          ∗ R10_reg ↦ saved_ptr_loc
          ∗ R11_reg ↦ valid_flag
          ∗ R12_reg ↦ ipe_sig_valid_src
          ∗ R13_reg ↦ ipe_struct_pointer_src

          ∗ asn_flag_valid
          ∗ asn_ptsto_word ipe_struct_pointer_src (low saved_ptr) (high saved_ptr)
          ∗ asn_ptsto_word saved_ptr_loc (low saved_ptr) (high saved_ptr)
      }}.

    Definition contract_evaluate_struct : BlockVerifierContract :=
      {{
           (* asn_init_pc evaluate_struct_start *)
⊤
         ∗ asn_ipe_registers_zero
         ∗ R6_reg ↦ saved_ptr +' 6
         ∗ R7_reg ↦ MPUIPC0_addr
         ∗ R8_reg ↦ MPUIPSEGB2_addr
         ∗ R9_reg ↦ MPUIPSEGB1_addr

         ∗ asn_ptsto_word (saved_ptr +' 4) (low conf_segb1) (high conf_segb1)
         (* ∗ asn_ptsto_word (saved_ptr +' 2) (low conf_segb2) (high conf_segb2) *)
         (* ∗ asn_ptsto_word saved_ptr (low conf_ipectl) (high conf_ipectl) *)
      }}
        [ mov_ir R6 (bv.of_Z (-2)%Z) R9
          (* mov_im R6 (bv.of_Z (-2)%Z) R9 *)
        (* ; mov_im R6 (bv.of_Z (-4)%Z) R8 *)
        (* ; mov_im R6 (bv.of_Z (-6)%Z) R7 *)
        (* ; jump JMP [bv 0x7] *) (* end *) ]
      {{ ⊤
         (*   asn_fin_pc end_addr *)

           (* MPUIPC0_reg    ↦ conf_ipectl *)
         (* ∗ MPUIPSEGB1_reg ↦ conf_segb1 *)
         (* ∗ MPUIPSEGB2_reg ↦ conf_segb2 *)

         (* ∗ R6_reg ↦ saved_ptr +' 6 *)
         (* ∗ R7_reg ↦ MPUIPC0_addr *)
         (* ∗ R8_reg ↦ MPUIPSEGB2_addr *)
         (* ∗ R9_reg ↦ MPUIPSEGB1_addr *)

         (* ∗ asn_ptsto_word (saved_ptr +' 4) (low conf_segb1) (high conf_segb1) *)
         (* ∗ asn_ptsto_word (saved_ptr +' 2) (low conf_segb2) (high conf_segb2) *)
         (* ∗ asn_ptsto_word saved_ptr (low conf_ipectl) (high conf_ipectl) *)
      }}.

    Lemma valid_start_bootcode : ValidBlockVerifierContract contract_start_bootcode.
    Proof. now symbolic_simpl. Qed.

    Lemma valid_transfer_if_valid_struct : ValidBlockVerifierContract contract_transfer_if_valid_struct.
    Proof. symbolic_simpl. intros. rewrite H. intuition. Qed.

    Lemma valid_evaluate_struct : ValidBlockVerifierContract contract_evaluate_struct.
    Proof.
      symbolic_simpl.
      repeat right.
      rewrite H. unfold bv.add. vm_compute.
      intuition; discriminate.
    Qed.

  End Bootcode.
End Examples.
