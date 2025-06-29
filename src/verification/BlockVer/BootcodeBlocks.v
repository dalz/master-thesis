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

Module BootcodeBlocks.
  Import Utils.

  Definition asn_ipe_registers_init {Σ} : Assertion Σ :=
      MPUIPC0_reg           ↦ term_val ty.wordBits [bv 0]
    ∗ ∃ "v", MPUIPSEGB1_reg ↦ term_var "v"
    ∗ ∃ "v", MPUIPSEGB2_reg ↦ term_var "v".

  Definition minimal_pre {Σ} : Assertion Σ :=
      ∃ "lif", LastInstructionFetch ↦ term_var "lif"
    ∗ ∃ "srcg1", SRCG1_reg ↦ term_var "srcg1"
    ∗ MPUCTL0_reg ↦ term_val ty.wordBits [bv 0xA500].

  Definition minimal_post {Σ} : Assertion Σ :=
    minimal_pre.

  Record BlockVerifierContract {Σ} :=
    MkBlockVerifierContract
      { precondition  : Assertion (Σ ▻ "a" :: ty.Address)
      ; instrs        : list ast_with_args
      ; postcondition : Assertion (Σ ▻ "a" :: ty.Address ▻ "an" :: ty.Address)
      }.

  Definition ValidBlockVerifierContract {Σ} (c : @BlockVerifierContract Σ) : Prop :=
  match c with
    {| precondition := pre; instrs := i; postcondition := post |} =>
      safeE (* VerificationCondition *) (postprocess
               (sblock_verification_condition
                  (minimal_pre ∗ pre)
                  i
                  (minimal_post ∗ post)
                  wnil))
  end.

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

  Definition asn_init_pc {Σ} (pc : bv 16) : Assertion (Σ ▻ "a" :: ty.Address) :=
    term_var "a" = term_val ty.Address pc.
  Definition asn_fin_pc {Σ} (pc : bv 16) : Assertion (Σ ▻ "an" :: ty.Address) :=
    term_var "an" = term_val ty.Address pc.

  Local Notation "v -' n" :=
    (term_binop bop.bvsub v (term_val ty.wordBits [bv n]))
    (at level 50).

  Definition asn_byte_zero {Σ} (b : Term Σ ty.byteBits) : Assertion Σ :=
    b = term_val ty.byteBits [bv 0].

  Definition saved_ptr_bv : bv 16 := [bv 0x4200].
  Definition isp_bv : bv 16 := [bv 0x4202].
  Definition saved_ptr {Σ} : Term Σ _ := term_val ty.Address saved_ptr_bv.
  Definition isp {Σ} : Term Σ _ := term_val ty.Address isp_bv.

  Definition byte_zero {Σ} : Term Σ _ := term_val ty.byteBits [bv 0].


  Definition valid_flag_bv : bv 16 := [bv 0xAAAA].
  Definition ipe_sig_valid_src_bv : bv 16 := [bv 0xFF88].
  Definition ipe_struct_pointer_src_bv : bv 16 := [bv 0xFF8A].
  Definition valid_flag {Σ} : Term Σ _ := term_val ty.wordBits valid_flag_bv.
  Definition ipe_sig_valid_src {Σ} : Term Σ _ := term_val ty.Address ipe_sig_valid_src_bv.
  Definition ipe_struct_pointer_src {Σ} : Term Σ _ := term_val ty.Address ipe_struct_pointer_src_bv.

  Definition start_bootcode_start : bv 16 := [bv 0].
  Definition transfer_if_valid_struct_start : bv 16 := [bv 0x4].
  Definition check_struct_start : bv 16 := [bv 0xC].
  Definition evaluate_struct_start : bv 16 := [bv 0x1A].
  Definition mass_erase_start : bv 16 := [bv 0x2E].
  Definition end_addr : bv 16 := [bv 0x3A].

  Definition start_bootcode_size := Z.to_nat (bv.unsigned (transfer_if_valid_struct_start - start_bootcode_start)).
  Definition transfer_if_valid_struct_size := Z.to_nat (bv.unsigned (check_struct_start - transfer_if_valid_struct_start)).
  Definition check_struct_size := Z.to_nat (bv.unsigned (evaluate_struct_start - check_struct_start)).
  Definition evaluate_struct_size := Z.to_nat (bv.unsigned (mass_erase_start - evaluate_struct_start)).
  Definition mass_erase_size := Z.to_nat (bv.unsigned (end_addr - mass_erase_start)).

  Definition asn_flag_valid {Σ} : Assertion Σ :=
    asn_ptsto_word ipe_sig_valid_src (low valid_flag) (high valid_flag).

  Definition block_start_bootcode :=
    [ tst_m R10
    ; jnz [bv 4] (* check_struct *)
    ]%list.

  Definition scontract_start_bootcode : BlockVerifierContract :=
    {{
          asn_init_pc start_bootcode_start
        ∗ asn_ipe_registers_init

        ∗ R10_reg ↦ saved_ptr
        ∗ (asn_ptsto_word saved_ptr byte_zero byte_zero
           ∨ asn_ptsto_word saved_ptr (low isp) (high isp))
    }}
      block_start_bootcode
    {{
          R10_reg ↦ saved_ptr
        ∗ asn_ipe_registers_init
        ∗ ( asn_ptsto_word saved_ptr byte_zero byte_zero
              ∗ asn_fin_pc transfer_if_valid_struct_start
            ∨ asn_ptsto_word saved_ptr (low isp) (high isp)
              ∗ asn_fin_pc check_struct_start)
    }}.


  Definition block_transfer_if_valid_struct :=
      [ cmp_rm R11 R12
      ; jnz [bv 0x18] (* end *)
      ; mov_mm R13 R10
      ]%list.

  Definition scontract_transfer_if_valid_struct : BlockVerifierContract :=
    {{
          asn_init_pc transfer_if_valid_struct_start

        ∗ asn_ipe_registers_init
        ∗ R10_reg ↦ saved_ptr
        ∗ R11_reg ↦ valid_flag
        ∗ R12_reg ↦ ipe_sig_valid_src
        ∗ R13_reg ↦ ipe_struct_pointer_src

        ∗ asn_flag_valid
        ∗ asn_ptsto_word ipe_struct_pointer_src (low isp) (high isp)
        ∗ asn_ptsto_word saved_ptr byte_zero byte_zero
    }}
      block_transfer_if_valid_struct
    {{
          asn_fin_pc check_struct_start

        ∗ asn_ipe_registers_init
        ∗ R10_reg ↦ saved_ptr
        ∗ R11_reg ↦ valid_flag
        ∗ R12_reg ↦ ipe_sig_valid_src
        ∗ R13_reg ↦ ipe_struct_pointer_src

        ∗ asn_flag_valid
        ∗ asn_ptsto_word ipe_struct_pointer_src (low isp) (high isp)
        ∗ asn_ptsto_word saved_ptr (low isp) (high isp)
    }}.

  Definition block_check_struct :=
      [ mov_mr R10 R6
      ; mov_rr R15 R14
      ; xor_ar R6 R14
      ; xor_ar R6 R14
      ; xor_ar R6 R14
      ; cmp_mr R6 R14
      ; jnz [bv 0xA] (* mass_erase_init *)
      ]%list.

  Definition scontract_check_struct : BlockVerifierContract :=
    {{
          asn_init_pc check_struct_start

        ∗ asn_ipe_registers_init
        ∗ R10_reg ↦ saved_ptr
        ∗ R15_reg ↦ term_val ty.wordBits [bv 0xFFFF]
        ∗ ∃ "v", R6_reg  ↦ term_var "v"
        ∗ ∃ "v", R14_reg ↦ term_var "v"

        ∗ asn_ptsto_word saved_ptr (low isp) (high isp)
        ∗ asn_ptsto_word isp        (term_var "ipectl_l") (term_var "ipectl_h")
        ∗ asn_ptsto_word (isp +' 2) (term_var "segb2_l") (term_var "segb2_h")
        ∗ asn_ptsto_word (isp +' 4) (term_var "segb1_l") (term_var "segb1_h")
        ∗ asn_ptsto_word (isp +' 6) (term_var "check_l") (term_var "check_h")
    }}
      block_check_struct
    {{
          ( asn_fin_pc evaluate_struct_start
          ∨ asn_fin_pc mass_erase_start)

        ∗ asn_ipe_registers_init
        ∗ R10_reg ↦ saved_ptr
        ∗ R15_reg ↦ term_val ty.wordBits [bv 0xFFFF]
        ∗ R6_reg ↦ isp +' 6
        ∗ ∃ "v", R14_reg ↦ term_var "v"

        ∗ asn_ptsto_word saved_ptr  (low isp) (high isp)
        ∗ asn_ptsto_word isp        (term_var "ipectl_l") (term_var "ipectl_h")
        ∗ asn_ptsto_word (isp +' 2) (term_var "segb2_l") (term_var "segb2_h")
        ∗ asn_ptsto_word (isp +' 4) (term_var "segb1_l") (term_var "segb1_h")
        ∗ asn_ptsto_word (isp +' 6) (term_var "check_l") (term_var "check_h")

    }} with [ "ipectl_l" :: ty.byteBits; "ipectl_h" :: ty.byteBits
            ; "segb2_l"  :: ty.byteBits; "segb2_h"  :: ty.byteBits
            ; "segb1_l"  :: ty.byteBits; "segb1_h"  :: ty.byteBits
            ; "check_l"  :: ty.byteBits; "check_h"  :: ty.byteBits ].

  Definition block_evaluate_struct :=
    [ mov_im R6 (bv.of_Z (-2)%Z) R9
    ; mov_im R6 (bv.of_Z (-4)%Z) R8
    ; mov_im R6 (bv.of_Z (-6)%Z) R7
    ; jump JMP [bv 0x6] (* end *)
    ]%list.

  Definition scontract_evaluate_struct : BlockVerifierContract :=
    {{
         asn_init_pc evaluate_struct_start

       ∗ asn_ipe_registers_init
       ∗ R6_reg ↦ isp +' 6
       ∗ R7_reg ↦ MPUIPC0_addr
       ∗ R8_reg ↦ MPUIPSEGB2_addr
       ∗ R9_reg ↦ MPUIPSEGB1_addr

       ∗ asn_ptsto_word (isp +' 4) (low (term_var "segb1")) (high (term_var "segb1"))
       ∗ asn_ptsto_word (isp +' 2) (low (term_var "segb2")) (high (term_var "segb2"))
       ∗ asn_ptsto_word isp (low (term_var "ipectl")) (high (term_var "ipectl"))
    }}
      block_evaluate_struct
    {{
         asn_fin_pc end_addr

       ∗ MPUIPC0_reg    ↦ term_var "ipectl"
       ∗ MPUIPSEGB1_reg ↦ term_var "segb1"
       ∗ MPUIPSEGB2_reg ↦ term_var "segb2"

       ∗ R6_reg ↦ isp +' 6
       ∗ R7_reg ↦ MPUIPC0_addr
       ∗ R8_reg ↦ MPUIPSEGB2_addr
       ∗ R9_reg ↦ MPUIPSEGB1_addr

       ∗ asn_ptsto_word (isp +' 4) (low (term_var "segb1")) (high (term_var "segb1"))
       ∗ asn_ptsto_word (isp +' 2) (low (term_var "segb2")) (high (term_var "segb2"))
       ∗ asn_ptsto_word isp (low (term_var "ipectl")) (high (term_var "ipectl"))
    }} with [ "ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits ].

  Lemma valid_start_bootcode : ValidBlockVerifierContract scontract_start_bootcode.
  Proof. now symbolic_simpl. Qed.

  Lemma valid_transfer_if_valid_struct : ValidBlockVerifierContract scontract_transfer_if_valid_struct.
  Proof. now symbolic_simpl. Qed.

  Lemma valid_check_struct : ValidBlockVerifierContract scontract_check_struct.
  Proof. now symbolic_simpl. Qed.

  Lemma valid_evaluate_struct : ValidBlockVerifierContract scontract_evaluate_struct.
  Proof.
    symbolic_simpl.
    intuition;
      unfold bv.app; unfold bv.take; unfold bv.drop;
      destruct bv.appView; reflexivity.
  Qed.

End BootcodeBlocks.
