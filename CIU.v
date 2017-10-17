Require Import Coq.Program.Program.
Require Import Coq.Program.Tactics.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Reals.Reals.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Lim_seq.
Require Import Coq.fourier.Fourier.
Require Import Autosubst.Autosubst.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Init.Wf.

Require Import Biorthogonality.Basics.
Require Import Biorthogonality.Measures.
Require Import Biorthogonality.Syntax.
Require Import Biorthogonality.OpSem.
Require Import Biorthogonality.MeasSem.
Require Import Biorthogonality.LogRel.
Require Import Biorthogonality.Compatibility.

Set Bullet Behavior "Strict Subproofs".

Open Scope nat.

(* Definition 7.1 (part 1) {def-ciu} *)
Definition CIU (e1 e2 : Expr) :=
  ECLOSED e1 /\
  ECLOSED e2 /\
  forall K,
    KCLOSED K ->
    Rbar_le (μeval_star e1 K) (μeval_star e2 K).

(* Definition 7.2 (part 1) {def-ciu}.
   Scoping results from use of CIU, see CIU_open_scope. *)
Definition CIU_open (Γ : Env) (e1 e2 : Expr) :=
  forall γ,
    SUBSCOPE Γ ⊢ γ ∷ 0 ->
    CIU e1.[γ] e2.[γ].

Lemma CIU_closed : forall {e1 e2},
    CIU e1 e2 ->
    ECLOSED e1 /\ ECLOSED e2.
Proof.
  intros.
  unfold CIU in H.
  intuition.
Qed.

Lemma CIU_closed_l : forall {e1 e2},
    CIU e1 e2 ->
    ECLOSED e1.
Proof.
  intros.
  apply CIU_closed in H.
  intuition.
Qed.

Hint Resolve CIU_closed_l.

Lemma CIU_closed_r : forall {e1 e2},
    CIU e1 e2 ->
    ECLOSED e2.
Proof.
  intros.
  apply CIU_closed in H.
  intuition.
Qed.

Hint Resolve CIU_closed_r.

Lemma CIU_open_scope : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2.
Proof.
  intros.
  unfold CIU_open in H.
  split;
    eapply sub_implies_scope_exp;
    eauto 3.
Qed.

Lemma CIU_open_scope_l : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e1.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.

Hint Resolve CIU_open_scope_l.

Lemma CIU_open_scope_r : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e2.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.

Hint Resolve CIU_open_scope_r.

(* Lemma 7.3 {lemma-e-subset-ciu} *)
Lemma Erel_implies_CIU : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    CIU_open Γ e1 e2.
Proof.
  intros.
  unfold CIU_open; intros.
  unfold CIU.
  split; [|split].
  - apply -> sub_preserves_scope_exp; eauto.
  - apply -> sub_preserves_scope_exp; eauto.
  - intros.
    rewrite μeval_lim_interchange.
    apply Sup_seq_bounded.
    intros.
    eapply H; eauto.
Qed.

(* Lemma 7.3 {lemma-exprel-absorbtive} *)
Lemma Erel_comp_CIU_implies_Erel : forall {Γ e1 e2 e3},
    Erel_open Γ e1 e2 ->
    CIU_open Γ e2 e3 ->
    Erel_open Γ e1 e3.
Proof.
  intros Γ e1 e2 e3 HErel HCIU.
  unfold Erel_open, Erel, Erel'.
  intros n γ1 γ2 HGrel.
  inversion HGrel as [Hγ1 [Hγ2 _]].
  split; [|split].
  - apply -> sub_preserves_scope_exp; eauto 3.
  - apply -> sub_preserves_scope_exp; eauto 3.
  - intros.
    eapply Rbar_le_trans.
    + eapply HErel; eauto.
    + eapply HCIU; eauto.
Qed.

(* Lemma 7.4 {lemma-ciu-subset-e} *)
Lemma CIU_implies_Erel : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    Erel_open Γ e1 e2.
Proof.
  intros.
  eapply Erel_comp_CIU_implies_Erel; eauto.
Qed.

(* Theorem 7.4 {thm-cu-euqals-e} *)
Theorem CIU_iff_Erel : forall {Γ e1 e2},
    CIU_open Γ e1 e2 <->
    Erel_open Γ e1 e2.
Proof.
  intuition (auto using CIU_implies_Erel, Erel_implies_CIU).
Qed.
