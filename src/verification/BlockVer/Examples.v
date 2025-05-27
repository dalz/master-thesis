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

  Definition asn_ipe_registers {Σ} : Assertion Σ :=
      ∃ "ipectl", MPUIPC0_reg          ↦ term_var "ipectl"
    ∗ ∃ "segb1" , MPUIPSEGB1_reg       ↦ term_var "segb1"
    ∗ ∃ "segb2" , MPUIPSEGB2_reg       ↦ term_var "segb2".

  Definition minimal_pre {Σ} (include_ipe : bool) : Assertion Σ :=
      ∃ "lif", LastInstructionFetch ↦ term_var "lif"
    ∗ ∃ "srcg1", SRCG1_reg ↦ term_var "srcg1"
    ∗ if include_ipe then asn_ipe_registers else ⊤
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
        asn_ipe_registers ∗
        R4_reg ↦ term_val ty.wordBits [bv 42] ∗
        ∃ "v", R5_reg ↦ term_var "v"
    }}

    [mov_rr R4 R5]

    {{
        asn_ipe_registers ∗
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

    Definition saved_ptr_loc {Σ} : Term Σ _ := term_val ty.Address [bv 0x4242].
    Definition valid_flag {Σ} : Term Σ _ := term_val ty.wordBits [bv 0xAAAA].
    Definition ipe_sig_valid_src {Σ} : Term Σ _ := term_val ty.Address [bv 0xFF88].
    Definition ipe_struct_pointer_src {Σ} : Term Σ _ := term_val ty.Address [bv 0xFF8A].

    Definition start_bootcode_start{Σ} : Term Σ _ := term_val ty.wordBits [bv 0].
    Definition transfer_if_valid_struct_start {Σ} : Term Σ _ := term_val ty.wordBits [bv 0x6].
    Definition check_struct_start {Σ} : Term Σ _ := term_val ty.wordBits [bv 0x14].
    Definition evaluate_struct_start {Σ} : Term Σ _ := term_val ty.wordBits [bv 0x24].
    Definition mass_erase_start {Σ} : Term Σ _ := term_val ty.wordBits [bv 0x38].
    Definition end_addr {Σ} : Term Σ _ := term_val ty.wordBits [bv 0x48].

    Definition asn_flag_valid {Σ} : Assertion Σ :=
      asn_ptsto_word ipe_sig_valid_src (low valid_flag) (high valid_flag).

    Definition contract_start_bootcode : BlockVerifierContract :=
      {{
            asn_init_pc start_bootcode_start

          ∗ R10_reg ↦ saved_ptr_loc
          ∗ asn_ptsto_word saved_ptr_loc (term_var "ptr_l") (term_var "ptr_h")
      }}
        [ tst_m R10
        ; jnz [bv 5] (* check_struct *) ]
      {{
            R10_reg ↦ saved_ptr_loc
          ∗ asn_ptsto_word saved_ptr_loc (term_var "ptr_l") (term_var "ptr_h")

          ∗ (( (*asn_byte_zero (term_var "ptr_l")
             ∗ asn_byte_zero (term_var "ptr_h")
             ∗ *)asn_fin_pc transfer_if_valid_struct_start)
            ∨ asn_fin_pc check_struct_start)
      }}
        with ["ptr_l" :: ty.byteBits; "ptr_h" :: ty.byteBits].

    Definition contract_transfer_if_valid_struct : BlockVerifierContract :=
      {{
            asn_init_pc transfer_if_valid_struct_start

          ∗ R10_reg ↦ saved_ptr_loc
          ∗ R11_reg ↦ valid_flag
          ∗ R12_reg ↦ ipe_sig_valid_src
          ∗ R13_reg ↦ ipe_struct_pointer_src
          ∗ asn_flag_valid
          ∗ asn_ptsto_word ipe_struct_pointer_src
              (term_var "struct_ptr_l") (term_var "struct_ptr_h")
          ∗ ∃ "l", ∃ "h", asn_ptsto_word saved_ptr_loc (term_var "l") (term_var "h")
      }}
        [ cmp_rm R11 R12
        ; jnz [bv 29]
        ; mov_mm R13 R10 ]
      {{
            R10_reg ↦ saved_ptr_loc
          ∗ R11_reg ↦ valid_flag
          ∗ R12_reg ↦ ipe_sig_valid_src
          ∗ R13_reg ↦ ipe_struct_pointer_src
          ∗ asn_flag_valid
          ∗ asn_ptsto_word ipe_struct_pointer_src
              (term_var "struct_ptr_l") (term_var "struct_ptr_h")

          ∗ asn_fin_pc check_struct_start
          ∗ asn_ptsto_word saved_ptr_loc (term_var "struct_ptr_l") (term_var "struct_ptr_h")
      }}
        with ["struct_ptr_l" :: ty.byteBits; "struct_ptr_h" :: ty.byteBits].

    Definition contract_evaluate_struct : BlockVerifierContract :=
      {{
           asn_init_pc evaluate_struct_start
         ∗ asn_ipe_registers

         ∗ R6_reg ↦ term_val ty.Address [bv 0x1000]
         ∗ asn_ptsto_word (term_val ty.Address [bv 0x1000]) (term_val ty.byteBits [bv 0]) (term_val ty.byteBits [bv 0])

         (* ∗ R7_reg ↦ MPUIPC0_addr *)
         (* ∗ R8_reg ↦ MPUIPSEGB2_addr *)
         (* ∗ R9_reg ↦ MPUIPSEGB1_addr *)

         (* ∗ R6_reg ↦ term_var "struct_ptr" +' 6 *)

         (* ∗ term_var "struct_ptr" = term_val ty.wordBits [bv 0x1000] *)

         (* (* struct doesn't overlap MPU register file *) *)
         (* (*    needs more preconditions to exclude overflow of struct_ptr + 6 *) *)
         (* (* ∗ (term_unsigned (term_var "struct_ptr" +' 6) < (term_val ty.int 0x05A0%Z) *) *)
         (* (*    ∨ term_val ty.int 0x05B0%Z <= term_unsigned (term_var "struct_ptr")) *) *)

         (* ∗ asn_ptsto_word (term_var "struct_ptr" +' 4) *)
         (*     (low (term_var "segb1")) (high (term_var "segb1")) *)
         (* ∗ asn_ptsto_word (term_var "struct_ptr" +' 2) *)
         (*     (low (term_var "segb2")) (high (term_var "segb2")) *)
         (* ∗ asn_ptsto_word (term_var "struct_ptr") *)
         (*     (low (term_var "ipectl")) (high (term_var "ipectl")) *)
      }}
        [ mov_rm R6 R6          (* fix offsets *)
          (* mov_im R6 (bv.of_Z (-2)%Z) R9 *)
        (* ; mov_im R6 (bv.of_Z (-4)%Z) R8 *)
        (* ; mov_im R6 (bv.of_Z (-6)%Z) R7 *)
        (* ; jump JMP [bv (* 0x08 *) 0x10] *) (* end *)]
      {{ ⊥
         (*   (* asn_fin_pc end_addr *) *)
         (*   PC_reg         ↦ end_addr *)
         (* ∗ MPUIPC0_reg    ↦ term_var "ipectl" *)
         (* ∗ MPUIPSEGB1_reg ↦ term_var "segb1" *)
         (* ∗ MPUIPSEGB2_reg ↦ term_var "segb2" *)

         (* ∗ R6_reg ↦ term_var "struct_ptr" +' 6 *)
         (* ∗ R7_reg ↦ MPUIPC0_addr *)
         (* ∗ R8_reg ↦ MPUIPSEGB2_addr *)
         (* ∗ R9_reg ↦ MPUIPSEGB1_addr *)
      }}
        with ["ipectl" :: ty.wordBits; "segb1" :: ty.wordBits; "segb2" :: ty.wordBits; "struct_ptr" :: ty.Address].

    Lemma valid_start_bootcode : ValidBlockVerifierContract contract_start_bootcode.
    Proof. vm_compute. Set Printing Depth 200. Unset Printing 
           (* 0xe/0x4 = 0x14 *)
           symbolic_simpl.
           repeat split; try lia.
           intuition.
           auto 10 with *.
           repeat split.

           vm_compute. Set Printing Depth 200.
    Qed.

    (* Lemma valid_transfer_if_valid_struct : ValidBlockVerifierContract contract_transfer_if_valid_struct. *)
    (* Proof. vm_compute.  *)

    Lemma valid_evaluate_struct : ValidBlockVerifierContractWithExplicitIPE contract_evaluate_struct.
    Proof.
      symbolic_simpl.
      repeat right.
      rewrite H. unfold bv.add. vm_compute.
      intuition; discriminate.
    Qed.

    (* TODO is check_byte_access's contract good enough? *)

  End Bootcode.
End Examples.

(*
{|
debug_consume_chunk_pathcondition :=
[formula_relop
bop.eq
(term_var
"struct_ptr" +' 0x4)
(term_binop
bop.bvand
(term_var
"struct_ptr" +' 0x4)
(term_val
ty.Address
[bv 0xfffe]));
formula_relop
bop.eq
(term_var
"struct_ptr" +' 0x2)
(term_binop
bop.bvand
(term_var
"struct_ptr" +' 0x2)
(term_val
ty.Address
[bv 0xfffe]));
formula_relop
bop.eq
(term_var
"struct_ptr")
(term_binop
bop.bvand
(term_var
"struct_ptr")
(term_val
ty.Address
[bv 0xfffe]));
formula_relop
bop.eq
(term_var "bh.1" @
term_var "bl.1")
(term_val
ty.Address
[bv 0xfffe]);
formula_relop
bop.eq
(term_binop
bop.bvadd
(term_var
"struct_ptr")
(term_var "bh.1" @
term_var "bl.1") +'
0x6)
(term_binop
bop.bvand
(term_binop
bop.bvadd
(term_var
"struct_ptr")
(term_var "bh.1" @
term_var "bl.1") +'
0x6)
(term_val
ty.Address
[bv 0xfffe]));
formula_relop
bop.eq
(term_binop
bop.bvadd
(term_var
"struct_ptr")
(term_var "bh.1" @
term_var "bl.1") +'
0x6)
(term_var
"struct_ptr" +' 0x4);
formula_relop
bop.eq
(term_binop
bop.bvor
(term_binop
bop.bvadd
(term_var
"struct_ptr")
(term_var "bh.1" @
term_var "bl.1") +'
0x6)
(term_val
ty.Address [bv 0x1]))
(term_binop
bop.bvor
(term_var
"struct_ptr" +' 0x4)
(term_val
ty.Address [bv 0x1]));
formula_relop
bop.le
(term_val ty.int
1456%Z)
(term_unsigned
(term_binop
bop.bvadd
(term_var
"struct_ptr")
(term_var "bh.1" @
term_var "bl.1") +'
0x6));
formula_relop
bop.le
(term_val ty.int
1456%Z)
(term_unsigned
(term_binop
bop.bvor
(term_binop
bop.bvadd
(term_var
"struct_ptr")
(term_var "bh.1" @
term_var "bl.1") +'
0x6)
(term_val
ty.Address [bv 0x1])))];
debug_consume_chunk_heap :=
[chunk_ptsreg
R9_reg
(term_vector_subrange
0 8
(term_var "segb1") @
term_vector_subrange
8 8
(term_var "segb1"));
chunk_ptsreg
LastInstructionFetch
(term_val
(ty.union Uwordbyte)
(Word [bv 0x0]));
chunk_ptsreg
MPUIPSEGB2_reg
(term_var "segb2.2");
chunk_ptsreg
MPUIPSEGB1_reg
(term_var "segb1.2");
chunk_ptsreg
MPUIPC0_reg
(term_var
"ipectl.2");
chunk_user ptstomem
[term_binop
bop.bvor
(term_binop
bop.bvadd
(term_var
"struct_ptr")
(term_var "bh.1" @
term_var "bl.1") +'
0x6)
(term_val
ty.Address [bv 0x1]);
term_vector_subrange
0 8
(term_var "segb1")];
chunk_user ptstomem
[term_binop
bop.bvadd
(term_var
"struct_ptr")
(term_var "bh.1" @
term_var "bl.1") +'
0x6;
term_vector_subrange
8 8
(term_var "segb1")];
chunk_user
ptstoinstr
[term_val
ty.Address
[bv 0x26];
term_union
Uinstr_or_data Kd
(term_var "bh.1" @
term_var "bl.1")];
chunk_ptsreg R6_reg
(term_var
"struct_ptr" +' 0x6);
chunk_user
ptstoinstr
[term_val
ty.Address
[bv 0x24];
term_union
Uinstr_or_data Kd
(term_var "bh" @
term_var "bl")];
chunk_user
encodes_instr
[term_var "bh" @
term_var "bl";
term_val
(ty.union Uast)
(DOUBLEOP MOV
WORD_INSTRUCTION R6
INDEXED_MODE R9
REGISTER_MODE)];
chunk_user ptstomem
[term_binop
bop.bvor
(term_var
"struct_ptr")
(term_val
ty.Address [bv 0x1]);
term_vector_subrange
0 8
(term_var "ipectl")];
chunk_user ptstomem
[term_var
"struct_ptr";
term_vector_subrange
8 8
(term_var "ipectl")];
chunk_user ptstomem
[term_binop
bop.bvor
(term_var
"struct_ptr" +' 0x2)
(term_val
ty.Address [bv 0x1]);
term_vector_subrange
0 8
(term_var "segb2")];
chunk_user ptstomem
[term_var
"struct_ptr" +' 0x2;
term_vector_subrange
8 8
(term_var "segb2")];
chunk_ptsreg R8_reg
(term_val
ty.Address
[bv 0x5ac]);
chunk_ptsreg R7_reg
(term_val
ty.Address
[bv 0x5aa]);
chunk_ptsreg
MPUIPSEGB2_reg
(term_var "segb2.1");
chunk_ptsreg
MPUIPSEGB1_reg
(term_var "segb1.1");
chunk_ptsreg
MPUIPC0_reg
(term_var
"ipectl.1")]%list;
debug_consume_chunk_chunk :=
chunk_user
ptstoinstr
[term_val
ty.Address
[bv 0x24];
term_val
(ty.union
Uinstr_or_data)
(I
(DOUBLEOP MOV
WORD_INSTRUCTION R6
INDEXED_MODE R9
REGISTER_MODE))]
|}

 *)
