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
Require Import Biorthogonality.LogRel.
Require Import Biorthogonality.Syntax.
Require Import Biorthogonality.OpSem.
Require Import Biorthogonality.MeasSem.

Set Bullet Behavior "Strict Subproofs".

Open Scope nat.

(* Vrel compatibility *)

(** Lemma 5: variables are value-compatible *)
Lemma Vrel_Var_compatible :
  forall Γ x,
    x < Γ ->
    Vrel_open Γ (Var x) (Var x).
Proof.
  unfold Vrel_open, Grel.
  cbn.
  intuition.
Qed.

Hint Resolve Vrel_Var_compatible.

Lemma Vrel_Const_compatible_closed :
  forall m r,
    Vrel m (Const r) (Const r).
Proof.
  intros.
  rewrite Vrel_Fix_eq.
  unfold Vrel_rec.
  intuition constructor.
Qed.

Hint Resolve Vrel_Const_compatible_closed.

Lemma Vrel_Const_compatible :
  forall Γ r,
    Vrel_open Γ (Const r) (Const r).
Proof.
  unfold Vrel_open, Grel.
  intros.
  cbn.
  apply Vrel_Const_compatible_closed.
Qed.

Hint Resolve Vrel_Const_compatible.

(** Lemma 6: λ-expressions are value-compatible *)
Lemma Vrel_Fun_compatible :
  forall Γ e1 e2,
    Erel_open (S Γ) e1 e2 ->
    Vrel_open Γ (Fun e1) (Fun e2).
Proof.
  intros.
  unfold Vrel_open; intros.
  inversion H0 as [? [? ?]].
  cbn.
  rewrite Vrel_Fix_eq.
  unfold Vrel_rec at 1.
  intuition idtac.
  - constructor.
    apply -> sub_preserves_scope_exp; eauto.
  - constructor.
    apply -> sub_preserves_scope_exp; eauto.
  - asimpl.
    eapply H.
    eauto.
Qed.

Hint Resolve Vrel_Fun_compatible.

(* Pitts Lemma 4.2 part 1 *)
Lemma Krel_cons :
  forall n (e1 e2 : Expr),
    (forall m v1 v2, m <= n -> Vrel m v1 v2 -> Erel m (e1.[v1/]) (e2.[v2/])) ->
    forall m K1 K2, m <= n -> Krel m K1 K2 -> Krel m (e1-:K1) (e2-:K2).
Proof.
  intros.
  destruct (Erel_closed (H m (Const 0) (Const 0) ltac:(auto) ltac:(auto)))
           as [Hclosed_e1 Hclosed_e2].
  apply sub_implies_scope_exp_1 in Hclosed_e1.
  apply sub_implies_scope_exp_1 in Hclosed_e2.
  unfold Krel, Krel'; intros.
  destruct (Krel_closed H1) as [Hclosed_K1 Hclosed_K2].
  split; [|split]; try solve [constructor; auto].
  intros.
  destruct (Vrel_closed H2) as [IsClosed_v1 IsClosed_v2].
  run_μeval_for 1.
  run_μeval_star_for 1.
  apply H with (m:=m0); eauto.
Qed.

Hint Resolve Krel_cons.

(* Pitts Lemma 4.2 part 1 *)
Lemma Expr_cons :
  forall n (e1 e2 : Expr),
    (forall m (Hmn : m <= n) v1 v2,
        Vrel m v1 v2 -> Erel m e1.[v1/] e2.[v2/]) ->
    forall m (Hmn : m <= n) e1' e2',
      Erel m e1' e2' ->
      Erel m (Seq e1' e1) (Seq e2' e2).
Proof.
  intros.
  destruct (Erel_closed H0) as [IsClosed_e1 IsClosed_e2].
  unfold Erel, Erel'.
  split; [|split];
    try solve [specialize (H 0 ltac:(auto) _ _ (Vrel_Const_compatible_closed 0 0));
               constructor; eauto using sub_implies_scope_exp_1].
  intros.
  run_μeval_for 1.
  run_μeval_star_for 1.
  eapply H0; eauto 6.
Qed.

Hint Resolve Expr_cons.

(** Lemma 7: e ::= v *)
Lemma Erel_Val_compatible_closed :
  forall {n v v'},
    Vrel n v v' ->
    Erel n v v'.
Proof.
  intros.
  unfold Erel, Erel'.
  pose proof (Vrel_possibilities H).
  intuition eauto;
    match goal with
    | [H : Krel' _ _ _ _ |- _] => apply H; eauto
    end.
Qed.

Hint Resolve Erel_Val_compatible_closed.

Lemma Erel_Val_compatible :
  forall {Γ v v'},
    Vrel_open Γ v v' ->
    Erel_open Γ v v'.
Proof.
  intros.
  unfold Erel_open, Vrel_open in *.
  auto.
Qed.

Hint Resolve Erel_Val_compatible.

Lemma Erel_Var_compatible :
  forall Γ x,
    x < Γ ->
    Erel_open Γ (Var x) (Var x).
Proof.
  auto.
Qed.

Hint Resolve Erel_Var_compatible.

Lemma Erel_Const_compatibile :
  forall Γ r,
    Erel_open Γ (Const r) (Const r).
Proof.
  auto.
Qed.

Hint Resolve Erel_Var_compatible.

(* Lemma 5: compatible under Fun *)
Lemma Erel_Fun_compatible :
  forall Γ e e',
    Erel_open (S Γ) e e' ->
    Erel_open Γ (Fun e) (Fun e').
Proof.
  auto.
Qed.

Hint Resolve Erel_Fun_compatible.

Lemma Erel_Seq_compatible :
  forall Γ (e1 e2 e1' e2': Expr),
    Erel_open (S Γ) e1 e2 ->
    Erel_open Γ e1' e2' ->
    Erel_open Γ (Seq e1' e1) (Seq e2' e2).
Proof.
  intros.
  unfold Erel_open.
  intros.
  cbn.
  eapply Expr_cons; auto.
  intros.
  asimpl.
  eauto.
Qed.

Hint Resolve Erel_Seq_compatible.

Lemma Vrel_open_Erel_open :
  forall Γ v v',
    Vrel_open Γ v v' -> Erel_open Γ v v'.
Proof.
  eauto.
Qed.

Hint Resolve Vrel_open_Erel_open.

Lemma Erel_App_compatible_closed : forall n v1 v1' v2 v2',
    Vrel n v1 v2 ->
    Vrel n v1' v2' ->
    Erel n (App v1 v1') (App v2 v2').
Proof.
  intros.
  destruct (Vrel_closed H).
  destruct (Vrel_closed H0).
  unfold Erel, Erel'.
  split; [|split];
    destruct (Vrel_possibilities H) as [[r [? ?]]|[b1 [b2 [? ?]]]];
    subst;
    try solve [constructor; auto];
    intros;
    try solve [constructor; auto;
               rewrite Vrel_Fix_eq in H0;
               unfold Vrel_rec at 1 in H0;
               destruct v1', v2';
               intuition].
  - run_μeval.
  - run_μeval_for 1.
    run_μeval_star_for 1.
    erewrite Vrel_Fix_eq in H.
    unfold Vrel_rec in H at 1.
    eapply H; eauto.
Qed.

Hint Resolve Erel_App_compatible_closed.

(* Lemma 8 *)
Lemma Erel_App_compatible : forall Γ v1 v1' v2 v2',
    Vrel_open Γ v1 v2 ->
    Vrel_open Γ v1' v2' ->
    Erel_open Γ (App v1 v1') (App v2 v2').
Proof.
  intros.
  unfold Vrel_open in H.
  unfold Vrel_open in H0.
  unfold Erel_open.
  asimpl.
  eauto.
Qed.

Hint Resolve Erel_App_compatible.

Lemma Erel_Op1_compatible_closed : forall n o v1 v2,
    Vrel n v1 v2 ->
    Erel n (Op1 o v1) (Op1 o v2).
Proof.
  intros.
  destruct (Vrel_closed H).
  unfold Erel, Erel'.
  split; [|split];
    destruct (Vrel_possibilities H) as [[r [? ?]]|[b1 [b2 [? ?]]]];
    subst;
    try solve [constructor; auto];
    intros;
    try solve [constructor; auto;
               rewrite Vrel_Fix_eq in H0;
               unfold Vrel_rec at 1 in H0;
               destruct v1', v2';
               intuition].
  - destruct m; auto.
    { rewrite μeval_0.
      apply μeval_star_nonnegative.
    }
    destruct o.
    + destruct (Req_EM_T 0 r); subst.
      * rewrite μeval_step_Op1_Log_0.
        apply μeval_star_nonnegative.
      * rewrite μeval_step_Op1_Log; auto.
        erewrite μeval_star_step_1; revgoals.
        intros.
        apply μeval_step_Op1_Log; auto.
        apply H2; auto.
    + rewrite μeval_step_Op1_Exp.
      erewrite μeval_star_step_1; revgoals.
      intros.
      apply μeval_step_Op1_Exp.
      apply H2; auto.
    + rewrite μeval_step_Op1_Realp_1.
      erewrite μeval_star_step_1; revgoals.
      intros.
      apply μeval_step_Op1_Realp_1.
      apply H2; auto.
  - destruct m; auto.
    { rewrite μeval_0.
      apply μeval_star_nonnegative.
    }
    destruct o;
      try solve [unfold μeval;
                 unfold eval;
                 cbn;
                 repeat rewrite integrate_0;
                 apply μeval_star_nonnegative].
    rewrite μeval_step_Op1_Realp_0.
    erewrite μeval_star_step_1; revgoals.
    intros.
    apply μeval_step_Op1_Realp_0.
    apply H2; auto.
Qed.

Hint Resolve Erel_Op1_compatible_closed.

Lemma Erel_Op1_compatible : forall Γ o v1 v2,
    Vrel_open Γ v1 v2 ->
    Erel_open Γ (Op1 o v1) (Op1 o v2).
Proof.
  intros.
  unfold Vrel_open in H.
  unfold Erel_open.
  asimpl.
  eauto.
Qed.

Hint Resolve Erel_Op1_compatible.

Lemma Erel_Op2_compatible_closed : forall n o v1 v1' v2 v2',
    Vrel n v1 v2 ->
    Vrel n v1' v2' ->
    Erel n (Op2 o v1 v1') (Op2 o v2 v2').
Proof.
  intros.
  destruct (Vrel_closed H).
  destruct (Vrel_closed H0).
  unfold Erel, Erel'.
  split; [|split];
    destruct (Vrel_possibilities H) as [[r [? ?]]|[b1 [b2 [? ?]]]];
    destruct (Vrel_possibilities H0) as [[r' [? ?]]|[b1' [b2' [? ?]]]];
    subst;
    try solve [constructor; auto];
    intros;
    try solve [constructor; auto;
               rewrite Vrel_Fix_eq in H0;
               unfold Vrel_rec at 1 in H0;
               destruct v1', v2';
               intuition
              |replace (μeval m _ _) with (Finite 0%R);
               [apply μeval_star_nonnegative|];
               destruct m;
               [rewrite μeval_0; auto|];
               destruct o;
                 unfold μeval;
                 unfold eval;
                 cbn;
                 repeat rewrite integrate_0;
                 auto].
  destruct m; auto.
  { rewrite μeval_0.
    apply μeval_star_nonnegative.
  }
  destruct o.
  + rewrite μeval_step_Op2_Plus.
    erewrite μeval_star_step_1; revgoals.
    intros.
    apply μeval_step_Op2_Plus.
    apply H5; auto.
  + rewrite μeval_step_Op2_Minus.
    erewrite μeval_star_step_1; revgoals.
    intros.
    apply μeval_step_Op2_Minus.
    apply H5; auto.
  + rewrite μeval_step_Op2_Times.
    erewrite μeval_star_step_1; revgoals.
    intros.
    apply μeval_step_Op2_Times.
    apply H5; auto.
  + destruct (Req_EM_T 0 r'); subst.
    * rewrite μeval_step_Op2_Div_0.
      apply μeval_star_nonnegative.
    * rewrite μeval_step_Op2_Div; auto.
      erewrite μeval_star_step_1; revgoals.
      intros.
      apply μeval_step_Op2_Div; auto.
      apply H5; auto.
  + destruct (Rlt_dec r r').
    * rewrite μeval_step_Op2_Lt_1; auto.
      erewrite μeval_star_step_1; revgoals.
      intros.
      apply μeval_step_Op2_Lt_1; auto.
      apply H5; auto.
    * rewrite μeval_step_Op2_Lt_0; auto using Rnot_lt_le.
      erewrite μeval_star_step_1; revgoals.
      intros.
      apply μeval_step_Op2_Lt_0;  auto using Rnot_lt_le.
      apply H5; auto.
  + destruct (Rle_dec r r').
    * rewrite μeval_step_Op2_Le_1; auto.
      erewrite μeval_star_step_1; revgoals.
      intros.
      apply μeval_step_Op2_Le_1; auto.
      apply H5; auto.
    * rewrite μeval_step_Op2_Le_0; auto using Rnot_le_lt.
      erewrite μeval_star_step_1; revgoals.
      intros.
      apply μeval_step_Op2_Le_0;  auto using Rnot_le_lt.
      apply H5; auto.
  + replace (μeval m _ K1 A) with (Finite 0);
      auto.
    destruct m; auto.
    * rewrite μeval_0; auto.
    * unfold μeval.
      unfold eval.
      destruct o;
        cbn;
        repeat rewrite integrate_0;
        auto.
  + replace (μeval m _ K1 A) with (Finite 0);
      auto.
    destruct m; auto.
    * rewrite μeval_0; auto.
    * unfold μeval.
      unfold eval.
      destruct o;
        cbn;
        repeat rewrite integrate_0;
        auto.
  + replace (μeval m _ K1 A) with (Finite 0);
      auto.
    destruct m; auto.
    * rewrite μeval_0; auto.
    * unfold μeval.
      unfold eval.
      destruct o;
        cbn;
        repeat rewrite integrate_0;
        auto.
Qed.

Hint Resolve Erel_Op2_compatible_closed.

Lemma Erel_Op2_compatible : forall Γ o v1 v1' v2 v2',
    Vrel_open Γ v1 v2 ->
    Vrel_open Γ v1' v2' ->
    Erel_open Γ (Op2 o v1 v1') (Op2 o v2 v2').
Proof.
  intros.
  unfold Vrel_open in H.
  unfold Erel_open.
  asimpl.
  eauto.
Qed.

Hint Resolve Erel_Op2_compatible.

Lemma Erel_Cond_compatible_closed : forall n vp vp' et et' ef ef',
    Vrel n vp vp' ->
    Erel n et et' ->
    Erel n ef ef' ->
    Erel n (Cond vp et ef) (Cond vp' et' ef').
Proof.
  intros.
  destruct (Vrel_closed H).
  destruct (Erel_closed H0).
  destruct (Erel_closed H1).
  unfold Erel, Erel'.
  split; [|split];
    destruct (Vrel_possibilities H) as [[r [? ?]]|[b1 [b2 [? ?]]]];
    subst;
    try solve [constructor; auto];
    intros;
    try solve [constructor; auto;
               rewrite Vrel_Fix_eq in H0;
               unfold Vrel_rec at 1 in H0;
               destruct v1', v2';
               intuition
              |replace (μeval m _ _) with (Finite 0%R);
               [apply μeval_star_nonnegative|];
               destruct m;
               [rewrite μeval_0; auto|];
               unfold μeval;
               unfold eval;
               cbn;
               repeat rewrite integrate_0;
               auto].
  destruct m; auto.
  { rewrite μeval_0.
    apply μeval_star_nonnegative.
  }
  + destruct (Rlt_dec 0 r).
    * rewrite μeval_step_Cond_true; auto.
      erewrite μeval_star_step_1; revgoals.
      intros.
      apply μeval_step_Cond_true; auto.
      apply H0; eauto.
    * rewrite μeval_step_Cond_false; auto using Rnot_lt_le.
      erewrite μeval_star_step_1; revgoals.
      intros.
      apply μeval_step_Cond_false; auto using Rnot_lt_le.
      apply H1; eauto.
  + replace (μeval m _ K1 A) with (Finite 0);
      auto.
    destruct m; auto.
    * rewrite μeval_0; auto.
    * unfold μeval.
      unfold eval.
      cbn.
      repeat rewrite integrate_0.
      auto.
Qed.

Hint Resolve Erel_Cond_compatible_closed.

Lemma Erel_Cond_compatible : forall Γ vp vp' et et' ef ef',
    Vrel_open Γ vp vp' ->
    Erel_open Γ et et' ->
    Erel_open Γ ef ef' ->
    Erel_open Γ (Cond vp et ef) (Cond vp' et' ef').
Proof.
  intros.
  unfold Vrel_open in H.
  unfold Erel_open.
  asimpl.
  eauto.
Qed.

Hint Resolve Erel_Cond_compatible.

(* Lemma 9 *)

(* Lemma 9 *)
Lemma Krel_Knil_refl : forall n,
    Krel n Knil Knil.
Proof.
  intros.
  unfold Krel, Krel'.
  intuition auto.
  destruct (Vrel_possibilities H) as [[r [? ?]]|[b1 [b2 [? ?]]]];
    subst;
    auto;
    run_μeval_for 1.
Qed.

Hint Resolve Krel_Knil_refl.

Instance Sup_seq_Proper_ext : Proper (pointwise_relation nat eq==>eq) Sup_seq.
Proof.
  unfold Proper, respectful, pointwise_relation.
  intros.
  apply Sup_seq_ext.
  auto.
Qed.
  
(* Lemma 13: compatible under factor *)
Lemma Erel_Factor_compatible_closed : forall n r1 r2,
    Vrel n r1 r2 ->
    Erel n (Factor r1) (Factor r2).
Proof.
  unfold Erel, Erel'.
  intuition eauto.
  destruct (Vrel_possibilities H) as [[r [? ?]]|[b1 [b2 [? ?]]]];
    subst;
    eauto;
    revgoals;
    try solve [run_μeval_for 1].
  destruct (Rbar_lt_dec 0%R r); revgoals.
  { replace (μeval m (Factor (Const r)) K1 A)
      with (Finite 0%R).
    apply μeval_star_nonnegative.
    unfold μeval.
    rewrite <- integrate_0.
    rewrite <- integrate_0.
    f_equal.
    extensionality σ2.
    f_equal.
    extensionality σ1.
    destruct m; auto.
    unfold eval.
    cbn.
    destruct Rlt_dec; try contradiction; auto.
  }
  run_μeval_for 1.
  replace (μeval_star _ _ _) with (Rbar_mult r (μeval_star (Const r) K2 A)).
  { apply Rbar_mult_le_compat_l; cbn in *; auto.
    apply H0; eauto.
  }
  rewrite μeval_lim_interchange with (e:=(Factor _)).
  rewrite Sup_seq_incr_1; auto.
  setoid_rewrite (μeval_step_Factor _ _ _ _ r0).
  rewrite Sup_seq_scal_l; cbn in *; auto.
  rewrite <- μeval_lim_interchange.
  auto.
Qed.

Hint Resolve Erel_Factor_compatible_closed.

Lemma Erel_Factor_compatible : forall Γ r1 r2,
    Vrel_open Γ r1 r2 ->
    Erel_open Γ (Factor r1) (Factor r2).
Proof.
  unfold Erel_open; intros.
  asimpl.
  eauto.
Qed.

Hint Resolve Erel_Factor_compatible.

Lemma Erel_Sample_compatible_closed : forall n,
    Erel n Sample Sample.
Proof.
  intros.
  unfold Erel.
  unfold Erel'.
  intuition auto.
  run_μeval_for 1; eauto.
  rewrite μeval_star_step_Sample.
  apply integrate_monotonic.
  intros.
  eapply H; auto.
Qed.

Hint Resolve Erel_Sample_compatible_closed.

Lemma Erel_Sample_compatible : forall Γ,
    Erel_open Γ Sample Sample.
Proof.
  unfold Erel_open.
  auto.
Qed.

Hint Resolve Erel_Sample_compatible.

(* Fundamental Theorem *)

Theorem Erel_Vrel_Fundamental_helper :
  forall (e : Expr),
    (forall Γ, EXP Γ ⊢ e -> Erel_open Γ e e) /\
    (forall Γ, VAL Γ ⊢ e -> Vrel_open Γ e e).
Proof.
  induction e;
    intuition auto;
    try solve_inversion.
  - eapply Erel_App_compatible; eauto.
  - eapply Erel_Seq_compatible; eauto.
  - eapply Erel_Op1_compatible; eauto.
  - eapply Erel_Op2_compatible; eauto.
  - eapply Erel_Cond_compatible; eauto.
Qed.

Theorem Erel_Fundamental :
  forall (e : Expr) (Γ : Env),
    EXP Γ ⊢ e ->
    Erel_open Γ e e.
Proof.
  intros.
  apply Erel_Vrel_Fundamental_helper.
  auto.
Qed.

Hint Resolve Erel_Fundamental.

Theorem Vrel_Fundamental :
  forall (v : Expr) (Γ : Env),
    VAL Γ ⊢ v ->
    Vrel_open Γ v v.
Proof.
  intros.
  apply Erel_Vrel_Fundamental_helper.
  auto.
Qed.

Hint Resolve Vrel_Fundamental.

Theorem Krel_Fundamental_closed :
  forall (K : Kont) (n : nat),
    KCLOSED K ->
    Krel n K K.
Proof.
  induction K; intros.
  - cbn.
    auto.
  - inversion H; subst.
    apply Krel_cons with (n:=n); auto; intros; asimpl.
    destruct (Vrel_closed H1) as [Hclosed_v1 Hclosed_v2].
    eapply Erel_Fundamental; eauto.
    unfold Grel.
    intuition idtac.
    + apply cons_scope; auto.
    + apply cons_scope; auto.
    + inversion H4; subst; auto.
      exfalso; auto.
Qed.

Hint Resolve Krel_Fundamental_closed.

Lemma Grel_ids : forall n, Grel n 0 ids ids.
Proof.
  intros.
  unfold Grel.
  intuition auto using scope_ids.
  exfalso; auto.
Qed.

Theorem Vrel_Fundamental_closed :
  forall (v : Expr),
    VCLOSED v ->
    forall n, Vrel n v v.
Proof.
  intros.
  replace v with (v.[ids]) by autosubst.
  eapply Vrel_Fundamental; eauto using Grel_ids.
Qed.

Hint Resolve Vrel_Fundamental_closed.

Theorem Erel_Fundamental_closed :
  forall (e : Expr),
    ECLOSED e ->
    forall n, Erel n e e.
Proof.
  intros.
  replace e with (e.[ids]) by autosubst.
  eapply Erel_Fundamental; eauto using Grel_ids.
Qed.

Hint Resolve Erel_Fundamental_closed.

Theorem Grel_Fundamental :
  forall (γ : var -> Expr) (Γ : Env),
    SUBSCOPE Γ ⊢ γ ∷ 0 ->
    forall n, Grel n Γ γ γ.
Proof.
  intros.
  unfold Grel.
  intuition.
Qed.

Hint Resolve Grel_Fundamental.
