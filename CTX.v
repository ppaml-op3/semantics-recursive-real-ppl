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
Require Import Init.Wf.

Require Import Biorthogonality.Basics.
Require Import Biorthogonality.Measures.
Require Import Biorthogonality.Syntax.
Require Import Biorthogonality.OpSem.
Require Import Biorthogonality.MeasSem.
Require Import Biorthogonality.LogRel.
Require Import Biorthogonality.Compatibility.
Require Import Biorthogonality.CIU.

Set Bullet Behavior "Strict Subproofs".

Open Scope nat.

Definition Adequate (R : forall (Γ : Env) (e1 e2 : Expr), Prop) :=
  forall e1 e2,
    R 0 e1 e2 ->
    forall A, Rbar_le (μeval_star e1 Knil A) (μeval_star e2 Knil A).

Definition IsReflexive (R : forall (Γ : Env) (e1 e2 : Expr), Prop) :=
  forall Γ e,
    EXP Γ ⊢ e ->
    R Γ e e.

Definition CompatibleFun (R : forall (Γ : Env) (e1 e2 : Expr), Prop) :=
  forall Γ e1 e2,
    R (S Γ) e1 e2 ->
    R Γ (Fun e1) (Fun e2).

Definition CompatibleApp (R : forall (Γ : Env) (e1 e2 : Expr), Prop) :=
  forall Γ f1 f2 v1 v2,
    VAL Γ ⊢ f1 ->
    VAL Γ ⊢ f2 ->
    VAL Γ ⊢ v1 ->
    VAL Γ ⊢ v2 ->
    R Γ f1 f2 ->
    R Γ v1 v2 ->
    R Γ (App f1 v1) (App f2 v2).

Definition CompatibleOp1 (R : forall (Γ : Env) (e1 e2 : Expr), Prop) :=
  forall Γ o v1 v2,
    VAL Γ ⊢ v1 ->
    VAL Γ ⊢ v2 ->
    R Γ v1 v2 ->
    R Γ (Op1 o v1) (Op1 o v2).

Definition CompatibleOp2 (R : forall (Γ : Env) (e1 e2 : Expr), Prop) :=
  forall Γ o v1 v2 v1' v2',
    VAL Γ ⊢ v1 ->
    VAL Γ ⊢ v2 ->
    VAL Γ ⊢ v1' ->
    VAL Γ ⊢ v2' ->
    R Γ v1 v2 ->
    R Γ v1' v2' ->
    R Γ (Op2 o v1 v1') (Op2 o v2 v2').

Definition CompatibleCond (R : forall (Γ : Env) (e1 e2 : Expr), Prop) :=
  forall Γ v1 v2 et1 et2 ef1 ef2,
    VAL Γ ⊢ v1 ->
    VAL Γ ⊢ v2 ->
    EXP Γ ⊢ et1 ->
    EXP Γ ⊢ et2 ->
    EXP Γ ⊢ ef1 ->
    EXP Γ ⊢ ef2 ->
    R Γ v1 v2 ->
    R Γ et1 et2 ->
    R Γ ef1 ef2 ->
    R Γ (Cond v1 et1 ef1) (Cond v2 et2 ef2).

Definition CompatibleFactor (R : forall (Γ : Env) (e1 e2 : Expr), Prop) :=
  forall Γ v1 v2,
    VAL Γ ⊢ v1 ->
    VAL Γ ⊢ v2 ->
    R Γ v1 v2 ->
    R Γ (Factor v1) (Factor v2).

Definition CompatibleSeq (R : forall (Γ : Env) (e1 e2 : Expr), Prop) :=
  forall Γ x1 x2 b1 b2,
    R Γ x1 x2 ->
    R (S Γ) b1 b2 ->
    R Γ (Seq x1 b1) (Seq x2 b2).

Definition IsPreCtxRel (R : forall (Γ : Env) (e1 e2 : Expr), Prop) :=
  (forall Γ e1 e2, R Γ e1 e2 -> EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
  Adequate R /\
  IsReflexive R /\
  (forall Γ, Transitive (R Γ)) /\
  CompatibleFun R /\
  CompatibleApp R /\
  CompatibleOp1 R /\
  CompatibleOp2 R /\
  CompatibleCond R /\
  CompatibleSeq R /\
  CompatibleFactor R.

Definition IsCtxRel (R : forall (Γ : Env) (e1 e2 : Expr), Prop) :=
  IsPreCtxRel R /\
  forall R',
    IsPreCtxRel R' ->
    forall Γ e1 e2,
      R' Γ e1 e2 -> R Γ e1 e2.

Lemma Krel_swap:
  forall (n : nat) (v1 v2 : Expr),
    Vrel n v1 v2 ->
    forall (K1 K2 : Kont),
      Krel n K1 K2 ->
      Krel (2 + n) (App (Var 0) v1-:K1) (App (Var 0) v2-:K2).
Proof.
  intros n v1 v2 HVrel_v1v2 K1 K2 HKrel.
  destruct (Vrel_closed HVrel_v1v2) as [Hclosed_v1 Hclosed_v2].
  destruct (Krel_closed HKrel) as [Hclosed_K1 Hclosed_K2].
  unfold Krel, Krel'.
  split; [|split];
    try solve [repeat constructor;
               auto using succ_ValScoped].
  intros m Hmn u1 u2 A HVrel_u1u2.
  destruct (Vrel_closed HVrel_u1u2) as [Hclosed_u1 Hclosed_u2].
  (* Cases where m < 2 are uninteresting. *)
  destruct m as [|[|]]; auto;
    try solve [run_μeval; auto].
  destruct (Vrel_possibilities HVrel_u1u2) as [[r [? ?]]
                                              |[b1 [b2 [? ?]]]];
                                               
    subst;
    auto;
    try solve [run_μeval; auto].
  - run_μeval.
    rewrite vclosed_ignores_sub with (e:=v1); auto.
    run_μeval_star_for 2; cbn.
    rewrite vclosed_ignores_sub with (e:=v2); auto.
    rewrite Vrel_Fix_eq in HVrel_u1u2.
    unfold Vrel_rec in HVrel_u1u2.
    apply HVrel_u1u2 with (m:=n0);
      eauto.
    + apply @Vrel_downclosed with (n:=n);
        auto.
    + apply @Krel_downclosed with (n:=n);
        auto.
Qed.

Lemma not_Erel_Const_Fun : forall n r b,
    ~ Erel (S n) (Const r) (Fun b).
Proof.
  intros n r b.
  unfold "~".
  intros Hrel.
  unfold Erel, Erel' in Hrel.
  destruct Hrel as [Hclosed_b [Hclosed_r Hrel]].
  specialize (Hrel 1 ltac:(auto) _ _ (Measurable_Singleton r) (Krel_Knil_refl _)).
  replace (μeval _ _ _ _) with (Finite 1%R) in Hrel; revgoals.
  { unfold μeval.
    cbn.
    repeat setoid_rewrite integrate_entropy_const.
    rewrite Measurable_Singleton_Indicator_1.
    f_equal.
    ring.
  }
  replace (μeval_star _ _ _) with (Finite 0%R) in Hrel; revgoals.
  { unfold μeval_star.
    unfold eval_star.
    do 2 setoid_rewrite <- Lim_seq_incr_1.
    cbn.
    repeat rewrite integrate_entropy_const.
    rewrite Lim_seq_const.
    auto.
  }
  cbn in Hrel; fourier.
Qed.

Lemma not_Erel_Fun_Const : forall n r b,
    ~ Erel (3 + n) (Fun b) (Const r).
Proof.
  intros n r b.
  unfold "~".
  intros Hrel.
  unfold Erel, Erel' in Hrel.
  destruct Hrel as [Hclosed_b [Hclosed_r Hrel]].
  remember ((Op1 Realp (Var 0)) -: Knil) as K.
  assert (Krel (3 + n) K K) as HK.
  { apply Krel_Fundamental_closed.
    subst.
    repeat constructor.
  }
  specialize (Hrel _ ltac:(auto) _ _ (Measurable_Singleton 0) HK).
  subst.
  clear HK.
  cbn in Hrel.
  run_μeval_H_1 Hrel.
  asimpl in Hrel.
  rewrite μeval_step_Op1_Realp_0 in Hrel.
  erewrite (μeval_star_step_end 4) in Hrel; revgoals.
  { intros.
    cbn.
    run_μeval_1.
    rewrite μeval_step_Op1_Realp_1.
    unfold μeval.
    unfold eval.
    cbn.
    repeat rewrite integrate_entropy_const.
    rewrite Measurable_Singleton_Indicator_0 by auto.
    replace (0 * 1)%R with 0%R by ring.
    reflexivity.
  }
  unfold μeval in Hrel.
  unfold eval in Hrel.
  cbn in Hrel.
  destruct n;
    cbn in Hrel;
    repeat rewrite integrate_entropy_const in Hrel;
    rewrite Measurable_Singleton_Indicator_1 in Hrel;
    replace (1 * 1)%R with 1%R in Hrel by ring;
    cbn in Hrel;
    auto.
Qed.

Lemma Erel_Fun_Const : forall n b r,
    Erel (2 + n) (Fun b) (Const r) ->
    forall v,
      VCLOSED v ->
      Erel n b.[v/] loop.
Proof.
  intros n b r Hrel v Hclosed_v.
  unfold Erel, Erel' in *.
  destruct Hrel as [Hclosed_b [Hclosed_r Hrel]].
  inversion Hclosed_b; subst.
  inversion H; subst.
  split; [|split]; auto.
  { apply -> sub_preserves_scope_exp; eauto.
  }
  { repeat constructor.
  }
  intros m Hmn K1 K2 A HKrel.
  rewrite μeval_star_loop_0.
  pose proof (succ_ValScoped Hclosed_v).
  destruct (Krel_closed HKrel) as [Hclosed_K1 Hclosed_K2].
  specialize (Hrel (2 + m) (ltac:(auto)) _ _ A
                   (Krel_Fundamental_closed (App (Var 0) v-:K1) _ ltac:(auto))).
  replace (μeval_star _ _ _) with (Finite 0%R) in Hrel;
    revgoals.
  { unfold μeval_star.
    unfold eval_star.
    do 3 setoid_rewrite <- Lim_seq_incr_1.
    cbn.
    repeat rewrite integrate_entropy_const.
    rewrite Lim_seq_const.
    trivial.
  }
  cbn in Hrel.
  run_μeval in Hrel.
  cbn in Hrel.
  run_μeval in Hrel.
  replace (v.[Fun b/]) with v in Hrel by (rewrite vclosed_ignores_sub; auto).
  auto.
Qed.

Lemma Erel_implies_Vrel_Const : forall n r1 r2,
    Erel (S n) (Const r1) (Const r2) ->
    Vrel n (Const r1) (Const r2).
Proof.
  intros.
  rewrite Vrel_Fix_eq.
  unfold Vrel_rec.
  intuition (try constructor).
  destruct (Req_dec r1 r2); auto.
  exfalso.

  unfold Erel, Erel' in H.
  destruct H as [Hclosed_r1 [Hclosed_r2 HErel]].
  specialize (HErel 1 ltac:(auto) _ _ (Measurable_Singleton r1) (Krel_Knil_refl 1)).

  unfold μeval in HErel.
  cbn in HErel.

  unfold μeval_star in HErel.
  unfold eval_star in HErel.
  do 2 setoid_rewrite <- Lim_seq_incr_1 in HErel.
  cbn in HErel.

  repeat setoid_rewrite integrate_entropy_const in HErel.
  rewrite Lim_seq_const in HErel.

  rewrite Measurable_Singleton_Indicator_1 in HErel.
  rewrite Measurable_Singleton_Indicator_0 in HErel; auto.
  cbn in HErel.
  fourier.
Qed.

Lemma Erel_implies_Vrel_closed : forall n v1 v2,
    VCLOSED v1 ->
    VCLOSED v2 ->
    Erel (3 + n) v1 v2 ->
    Vrel n v1 v2.
Proof.
  intros.
  destruct v1, v2;
    try solve_inversion;
    auto.
  - apply Erel_implies_Vrel_Const.
    eauto.
  - apply not_Erel_Const_Fun in H1.
    contradiction.
  - apply not_Erel_Fun_Const in H1.
    contradiction.
  - rewrite Vrel_Fix_eq.
    unfold Vrel_rec.
    intuition idtac.
    unfold Erel, Erel' in *.
    destruct H1 as [_ [_ H1]].
    destruct (Vrel_closed H2).
    intuition idtac.
    { inversion H; subst.
      apply -> sub_preserves_scope_exp; eauto.
    }
    { inversion H0; subst.
      apply -> sub_preserves_scope_exp; eauto.
    }
    remember (App (Var 0) v1'-:K1) as K1'.
    remember (App (Var 0) v2'-:K2) as K2'.
    assert (Krel (2 + m0) K1' K2').
    { subst.
      apply Krel_swap.
      - apply @Vrel_downclosed with (n:=m); auto.
      - auto.
    } 
    specialize (H1 (2 + m0) ltac:(auto) _ _ A H6).
    subst.
    cbn in H1.
    run_μeval in H1; asimpl in H1.
    rewrite vclosed_ignores_sub with (e:=v1') in H1; auto.
    run_μeval in H1.
    erewrite (μeval_star_step 2) in H1; revgoals.
    { intros.
      cbn.
      run_μeval.
      reflexivity.
    }
    rewrite vclosed_ignores_sub with (e:=v2') in H1; auto.
Qed.

Lemma Erel_implies_Vrel : forall v1 v2,
    VCLOSED v1 ->
    VCLOSED v2 ->
    Erel_open 0 v1 v2 ->
    Vrel_open 0 v1 v2.
Proof.
  intros.
  unfold Erel_open in H1.
  unfold Vrel_open.
  intros.
  apply Erel_implies_Vrel_closed.
  - apply -> sub_preserves_scope_val; eauto.
    unfold Grel in H2.
    intuition idtac.
  - apply -> sub_preserves_scope_val; eauto.
    unfold Grel in H2.
    intuition idtac.
  - intros.
    apply H1.
    unfold Grel.
    intuition idtac;
      unfold SubScoped; intuition.
Qed.

Lemma Erel_open_closed : forall Γ e1 e2,
    (forall γ, SUBSCOPE Γ ⊢ γ ∷ 0 -> Erel_open 0 e1.[γ] e2.[γ]) <->
    Erel_open Γ e1 e2.
Proof.
  split.
  { intros.
    apply CIU_iff_Erel.
    unfold CIU_open.
    intros.
    enough (forall γ', SUBSCOPE 0 ⊢ γ' ∷ 0 -> CIU e1.[γ].[γ'] e2.[γ].[γ']).
    { specialize (H1 ids).
      asimpl in H1.
      eapply H1.
      apply scope_ids.
    }
    change (CIU_open 0 e1.[γ] e2.[γ]).
    apply CIU_iff_Erel.
    apply H.
    auto.
  }
  { intros.
    destruct (Erel_open_scope H).
    assert (ECLOSED e1.[γ]) by (apply -> sub_preserves_scope_exp; eauto).
    assert (ECLOSED e2.[γ]) by (apply -> sub_preserves_scope_exp; eauto).
    unfold Erel_open.
    intros.
    replace γ1 with (upn 0 γ1) by auto.
    replace γ2 with (upn 0 γ2) by auto.
    repeat rewrite escoped_ignores_sub;
      try solve [apply -> sub_preserves_scope_val;
                 eauto
                |eauto].
  }
Qed.

Theorem Erel_IsPreCtxRel : IsPreCtxRel Erel_open.
Proof.
  unfold IsPreCtxRel.
  intuition idtac.
  - eapply Erel_open_scope in H.
    intuition idtac.
  - eapply Erel_open_scope in H.
    intuition idtac.
  - unfold Adequate.
    intros.
    apply CIU_iff_Erel in H.
    unfold CIU_open, CIU in H.
    specialize (H ids (scope_ids 0)).
    asimpl in H.
    apply H.
    constructor.
  - unfold IsReflexive.
    intros.
    apply Erel_Fundamental.
    auto.
  - unfold Transitive.
    intros.
    apply CIU_iff_Erel.
    apply CIU_iff_Erel in H.
    apply CIU_iff_Erel in H0.
    unfold CIU_open in *.
    intros.
    specialize (H γ H1).
    specialize (H0 γ H1).
    unfold CIU in *.
    intuition idtac.
    specialize (H5 K A H4).
    specialize (H6 K A H4).
    eapply Rbar_le_trans; eauto.
  - unfold CompatibleFun.
    intros.
    eauto.
  - unfold CompatibleApp.
    intros.
    apply Erel_open_closed.
    intros.
    apply Erel_App_compatible.
    + apply Erel_implies_Vrel;
        try solve [apply -> sub_preserves_scope_val;
                   eauto].
      eapply Erel_open_closed; eauto.
    + apply Erel_implies_Vrel;
        try solve [apply -> sub_preserves_scope_val;
                   eauto].
      eapply Erel_open_closed; eauto.
  - unfold CompatibleOp1.
    intros.
    apply Erel_open_closed.
    intros.
    apply Erel_Op1_compatible.
    apply Erel_implies_Vrel;
      try solve [apply -> sub_preserves_scope_val;
                 eauto].
    eapply Erel_open_closed; eauto.
  - unfold CompatibleOp2.
    intros.
    apply Erel_open_closed.
    intros.
    apply Erel_Op2_compatible.
    + apply Erel_implies_Vrel;
        try solve [apply -> sub_preserves_scope_val;
                   eauto].
      eapply Erel_open_closed; eauto.
    + apply Erel_implies_Vrel;
        try solve [apply -> sub_preserves_scope_val;
                   eauto].
      eapply Erel_open_closed; eauto.
  - unfold CompatibleCond.
    intros.
    apply Erel_open_closed.
    intros.
    apply Erel_Cond_compatible;
      try solve [eapply Erel_open_closed; eauto].
    apply Erel_implies_Vrel;
      try solve [apply -> sub_preserves_scope_val;
                 eauto].
    eapply Erel_open_closed; eauto.
  - unfold CompatibleSeq.
    intros.
    apply Erel_Seq_compatible; auto.
  - unfold CompatibleFactor.
    intros.
    apply Erel_open_closed.
    intros.
    apply Erel_Factor_compatible.
    apply Erel_implies_Vrel;
      try solve [apply -> sub_preserves_scope_val;
                 eauto].
    eapply Erel_open_closed; eauto.
Qed.

Corollary CIU_IsPreCtxRel : IsPreCtxRel CIU_open.
Proof.
  pose proof Erel_IsPreCtxRel.
  unfold IsPreCtxRel in *.
  intuition idtac.
  - apply CIU_iff_Erel in H9.
    apply H0 in H9.
    intuition.
  - apply CIU_iff_Erel in H9.
    apply H0 in H9.
    intuition.
  - unfold Adequate.
    intros.
    apply CIU_iff_Erel in H9.
    apply H in H9.
    auto.
  - unfold IsReflexive.
    intros.
    apply CIU_iff_Erel.
    apply H1.
    auto.
  - unfold Transitive.
    intros.
    apply CIU_iff_Erel.
    apply CIU_iff_Erel in H9.
    apply CIU_iff_Erel in H11.
    eapply H2; eauto.
  - unfold CompatibleFun.
    intros.
    apply CIU_iff_Erel.
    apply CIU_iff_Erel in H9.
    eapply H3; eauto.
  - unfold CompatibleApp.
    intros.
    apply CIU_iff_Erel.
    apply CIU_iff_Erel in H14.
    apply CIU_iff_Erel in H15.
    eapply H4; eauto.
  - unfold CompatibleOp1.
    intros.
    apply CIU_iff_Erel.
    apply CIU_iff_Erel in H12.
    eapply H5; eauto.
  - unfold CompatibleOp2.
    intros.
    apply CIU_iff_Erel.
    apply CIU_iff_Erel in H14.
    apply CIU_iff_Erel in H15.
    eapply H6; eauto.
  - unfold CompatibleCond.
    intros.
    apply CIU_iff_Erel.
    apply CIU_iff_Erel in H16.
    apply CIU_iff_Erel in H17.
    apply CIU_iff_Erel in H18.
    eapply H7; eauto.
  - unfold CompatibleSeq.
    intros.
    apply CIU_iff_Erel.
    apply CIU_iff_Erel in H9.
    apply CIU_iff_Erel in H11.
    eapply H8; eauto.
  - unfold CompatibleFactor.
    intros.
    apply CIU_iff_Erel.
    apply CIU_iff_Erel in H12.
    eapply H10; eauto.
Qed.

(* Lemma 8.6 {lemma-beta-value-ciu} *)
Lemma CIU_beta_value : forall {Γ b v},
    EXP S Γ ⊢ b ->
    VAL Γ ⊢ v ->
    (CIU_open Γ b.[v/] (App (Fun b) v) /\ 
     CIU_open Γ (App (Fun b) v) b.[v/]).
Proof.
  unfold CIU_open.
  intros.
  asimpl.
  unfold CIU.
  intuition idtac.
  - apply -> sub_preserves_scope_exp; try eassumption.
    apply -> sub_preserves_scope_exp; eauto.
  - constructor.
    + constructor.
      apply -> sub_preserves_scope_exp; eauto.
    + apply -> sub_preserves_scope_val; eauto.
  - apply Rbar_le_eq.
    symmetry.
    apply pure_steps_preserve_μeval_star.
    intros.
    asimpl.
    auto.
  - constructor.
    + constructor.
      apply -> sub_preserves_scope_exp; eauto.
    + apply -> sub_preserves_scope_val; eauto.
  - apply -> sub_preserves_scope_exp; try eassumption.
    apply -> sub_preserves_scope_exp; eauto.
  - apply Rbar_le_eq.
    apply pure_steps_preserve_μeval_star.
    intros.
    asimpl.
    auto.
Qed.

Lemma CTX_closed_under_substitution : forall {Γ e1 e2 v CTX},
    IsCtxRel CTX ->
    VAL Γ ⊢ v ->
    CTX (S Γ) e1 e2 ->
    CTX Γ e1.[v/] e2.[v/].
Proof.
  intros Γ e1 e2 v CTX HCtx Hscope_v HCtx_e1e2.
  destruct HCtx as [HCtx Hbiggest].
  destruct HCtx as [Rscope [Radequate [Rrefl [Rtrans [RFun [RApp [RSeq RFactor]]]]]]].
  destruct (Rscope _ _ _ HCtx_e1e2) as [Hscope_e1 Hscope_e2].
  pose proof (CIU_beta_value Hscope_e1 Hscope_v).
  pose proof (CIU_beta_value Hscope_e2 Hscope_v).
  destruct H as [? _].
  destruct H0 as [_ ?].
  apply CIU_iff_Erel in H.
  apply CIU_iff_Erel in H0.
  apply Hbiggest in H; auto using Erel_IsPreCtxRel.
  apply Hbiggest in H0; auto using Erel_IsPreCtxRel.
  eapply Rtrans in H.
  eapply H.
  eapply Rtrans; revgoals.
  eapply H0.
  auto.
Qed.

Lemma bigger_implies_IsCtxRel : forall E R,
    IsCtxRel R ->
    IsPreCtxRel E ->
    (forall Γ e1 e2, R Γ e1 e2 -> E Γ e1 e2) ->
    IsCtxRel E.
Proof.
  intros.
  split; auto.
  intros.
  apply H1.
  destruct H.
  eapply H4.
  - exact H2.
  - auto.
Qed.

(*** Concrete ctx *)

Inductive Ctx :=
| Ctx_hole : Ctx
| Ctx_Fun : forall (b : Ctx), Ctx
| Ctx_App_f : forall (f : Ctx) (v : Expr), Ctx
| Ctx_App_v : forall (f : Expr) (v : Ctx), Ctx
| Ctx_Op1 : forall (o : EOp1) (v : Ctx), Ctx
| Ctx_Op2_1 : forall (o : EOp2) (v1 : Ctx) (v2 : Expr), Ctx
| Ctx_Op2_2 : forall (o : EOp2) (v1 : Expr) (v2 : Ctx), Ctx
| Ctx_Cond_p : forall  (vp : Ctx) (et : Expr) (ef : Expr), Ctx
| Ctx_Cond_t : forall  (vp : Expr) (et : Ctx) (ef : Expr), Ctx
| Ctx_Cond_f : forall  (vp : Expr) (et : Expr) (ef : Ctx), Ctx
| Ctx_Seq_x : forall (x : Ctx) (b : Expr), Ctx
| Ctx_Seq_b : forall (x : Expr) (b : Ctx), Ctx
| Ctx_Factor : forall (r : Ctx), Ctx.

Fixpoint plug (C : Ctx) (e : Expr) :=
  match C with
  | Ctx_hole => e
  | Ctx_Fun b => Fun (plug b e)
  | Ctx_App_f f v => App (plug f e) v
  | Ctx_App_v f v => App f (plug v e)
  | Ctx_Op1 o v => Op1 o (plug v e)
  | Ctx_Op2_1 o v1 v2 => Op2 o (plug v1 e) v2
  | Ctx_Op2_2 o v1 v2 => Op2 o v1 (plug v2 e)
  | Ctx_Cond_p vp et ef => Cond (plug vp e) et ef
  | Ctx_Cond_t vp et ef => Cond vp (plug et e) ef
  | Ctx_Cond_f vp et ef => Cond vp et (plug ef e)
  | Ctx_Seq_x x b => Seq (plug x e) b
  | Ctx_Seq_b x b => Seq x (plug b e)
  | Ctx_Factor r => Factor (plug r e)
  end.

Fixpoint plugc (Couter Cinner : Ctx) :=
  match Couter with
  | Ctx_hole => Cinner
  | Ctx_Fun b => Ctx_Fun (plugc b Cinner)
  | Ctx_App_f f v => Ctx_App_f (plugc f Cinner) v
  | Ctx_App_v f v => Ctx_App_v f (plugc v Cinner)
  | Ctx_Op1 o v => Ctx_Op1 o (plugc v Cinner)
  | Ctx_Op2_1 o v1 v2 => Ctx_Op2_1 o (plugc v1 Cinner) v2
  | Ctx_Op2_2 o v1 v2 => Ctx_Op2_2 o v1 (plugc v2 Cinner)
  | Ctx_Cond_p vp et ef => Ctx_Cond_p (plugc vp Cinner) et ef
  | Ctx_Cond_t vp et ef => Ctx_Cond_t vp (plugc et Cinner) ef
  | Ctx_Cond_f vp et ef => Ctx_Cond_f vp et (plugc ef Cinner)
  | Ctx_Seq_x x b => Ctx_Seq_x (plugc x Cinner) b
  | Ctx_Seq_b x b => Ctx_Seq_b x (plugc b Cinner)
  | Ctx_Factor r => Ctx_Factor (plugc r Cinner)
  end.

Lemma plug_assoc : forall C1 C2 e,
    plug C1 (plug C2 e) =
    plug (plugc C1 C2) e.
Proof.
  induction C1;
    intros;
    cbn;
    auto;
    rewrite IHC1;
    auto.
Qed.

Reserved Notation "'EECTX' Γh ⊢ C ∷ Γ" (at level 60).
Reserved Notation "'VECTX' Γh ⊢ C ∷ Γ" (at level 60).

Inductive EECtxScope (Γh : Env) : Env -> Ctx -> Prop :=
| CEScope_hole : EECTX Γh ⊢ Ctx_hole ∷ Γh 
| CEScope_App_f : forall Γ C v,
    VECTX Γh ⊢ C ∷ Γ -> 
    VAL Γ ⊢ v ->
    EECTX Γh ⊢ Ctx_App_f C v ∷ Γ
| CEScope_App_v : forall Γ f C,
    VAL Γ ⊢ f ->
    VECTX Γh ⊢ C ∷ Γ -> 
    EECTX Γh ⊢ Ctx_App_v f C ∷ Γ
| CEScope_Op1 : forall Γ o C,
    VECTX Γh ⊢ C ∷ Γ -> 
    EECTX Γh ⊢ Ctx_Op1 o C ∷ Γ
| CEScope_Op2_1 : forall Γ o C v2,
    VECTX Γh ⊢ C ∷ Γ -> 
    VAL Γ ⊢ v2 ->
    EECTX Γh ⊢ Ctx_Op2_1 o C v2 ∷ Γ
| CEScope_Op2_2 : forall Γ o v1 C,
    VAL Γ ⊢ v1 ->
    VECTX Γh ⊢ C ∷ Γ -> 
    EECTX Γh ⊢ Ctx_Op2_2 o v1 C ∷ Γ
| CEScope_Cond_p : forall Γ C et ef,
    VECTX Γh ⊢ C ∷ Γ -> 
    EXP Γ ⊢ et ->
    EXP Γ ⊢ ef ->
    EECTX Γh ⊢ Ctx_Cond_p C et ef ∷ Γ
| CEScope_Cond_t : forall Γ vp C ef,
    VAL Γ ⊢ vp ->
    EECTX Γh ⊢ C ∷ Γ -> 
    EXP Γ ⊢ ef ->
    EECTX Γh ⊢ Ctx_Cond_t vp C ef ∷ Γ
| CEScope_Cond_f : forall Γ vp et C,
    VAL Γ ⊢ vp ->
    EXP Γ ⊢ et ->
    EECTX Γh ⊢ C ∷ Γ -> 
    EECTX Γh ⊢ Ctx_Cond_f vp et C ∷ Γ
| CEScope_Seq_x : forall Γ C b,
    EECTX Γh ⊢ C ∷ Γ -> 
    EXP S Γ ⊢ b ->
    EECTX Γh ⊢ Ctx_Seq_x C b ∷ Γ
| CEScope_Seq_b : forall Γ x C,
    EXP Γ ⊢ x ->
    EECTX Γh ⊢ C ∷ S Γ -> 
    EECTX Γh ⊢ Ctx_Seq_b x C ∷ Γ
| CEScope_Val : forall Γ C,
    VECTX Γh ⊢ C ∷ Γ -> 
    EECTX Γh ⊢ C ∷ Γ
with VECtxScope (Γh : Env) : Env -> Ctx -> Prop :=
| CEScope_Fun : forall Γ C,
    EECTX Γh ⊢ C ∷ (S Γ) ->
    VECTX Γh ⊢ Ctx_Fun C ∷ Γ
where
"'EECTX' Γh ⊢ C ∷ Γ" := (EECtxScope Γh Γ C)
and
"'VECTX' Γh ⊢ C ∷ Γ" := (VECtxScope Γh Γ C).

Lemma plug_preserves_scope_exp : forall {Γh C Γ e},
    (EECTX Γh ⊢ C ∷ Γ ->
     EXP Γh ⊢ e ->
     EXP Γ ⊢ plug C e) /\
    (VECTX Γh ⊢ C ∷ Γ ->
     EXP Γh ⊢ e ->
     VAL Γ ⊢ plug C e).
Proof.
  induction C;
    split;
    intros;
    inversion H; subst;
    cbn;
    try solve_inversion;
    auto;
    constructor;
    firstorder idtac.
  constructor 3.
  inversion H1; subst.
  firstorder idtac.
Qed.

Lemma plugc_preserves_scope_exp : forall {Γh Couter Γ Cinner Γ'},
    (EECTX Γ' ⊢ Couter ∷ Γ ->
     EECTX Γh ⊢ Cinner ∷ Γ' ->
     EECTX Γh ⊢ plugc Couter Cinner ∷ Γ) /\
    (VECTX Γ' ⊢ Couter ∷ Γ ->
     EECTX Γh ⊢ Cinner ∷ Γ' ->
     VECTX Γh ⊢ plugc Couter Cinner ∷ Γ).
Proof.
  induction Couter;
    split;
    intros;
    inversion H; subst;
    cbn;
    try solve_inversion;
    auto;
    constructor;
    firstorder idtac.
  constructor.
  inversion H1; subst.
  firstorder idtac.
Qed.

Reserved Notation "'EVCTX' Γh ⊢ C ∷ Γ" (at level 60).
Reserved Notation "'VVCTX' Γh ⊢ C ∷ Γ" (at level 60).

Inductive EVCtxScope (Γh : Env) : Env -> Ctx -> Prop :=
| CVScope_App_f : forall Γ C v,
    VVCTX Γh ⊢ C ∷ Γ -> 
    VAL Γ ⊢ v ->
    EVCTX Γh ⊢ Ctx_App_f C v ∷ Γ
| CVScope_App_v : forall Γ f C,
    VAL Γ ⊢ f ->
    VVCTX Γh ⊢ C ∷ Γ -> 
    EVCTX Γh ⊢ Ctx_App_v f C ∷ Γ
| CVScope_Op1 : forall Γ o C,
    VVCTX Γh ⊢ C ∷ Γ -> 
    EVCTX Γh ⊢ Ctx_Op1 o C ∷ Γ
| CVScope_Op2_1 : forall Γ o C v2,
    VVCTX Γh ⊢ C ∷ Γ -> 
    VAL Γ ⊢ v2 ->
    EVCTX Γh ⊢ Ctx_Op2_1 o C v2 ∷ Γ
| CVScope_Op2_2 : forall Γ o v1 C,
    VAL Γ ⊢ v1 ->
    VVCTX Γh ⊢ C ∷ Γ -> 
    EVCTX Γh ⊢ Ctx_Op2_2 o v1 C ∷ Γ
| CVScope_Cond_p : forall Γ C et ef,
    VVCTX Γh ⊢ C ∷ Γ -> 
    EXP Γ ⊢ et ->
    EXP Γ ⊢ ef ->
    EVCTX Γh ⊢ Ctx_Cond_p C et ef ∷ Γ
| CVScope_Cond_t : forall Γ vp C ef,
    VAL Γ ⊢ vp ->
    EVCTX Γh ⊢ C ∷ Γ -> 
    EXP Γ ⊢ ef ->
    EVCTX Γh ⊢ Ctx_Cond_t vp C ef ∷ Γ
| CVScope_Cond_f : forall Γ vp et C,
    VAL Γ ⊢ vp ->
    EXP Γ ⊢ et ->
    EVCTX Γh ⊢ C ∷ Γ -> 
    EVCTX Γh ⊢ Ctx_Cond_f vp et C ∷ Γ
| CVScope_Seq_x : forall Γ C b,
    EVCTX Γh ⊢ C ∷ Γ -> 
    EXP S Γ ⊢ b ->
    EVCTX Γh ⊢ Ctx_Seq_x C b ∷ Γ
| CVScope_Seq_b : forall Γ x C,
    EXP Γ ⊢ x ->
    EVCTX Γh ⊢ C ∷ S Γ -> 
    EVCTX Γh ⊢ Ctx_Seq_b x C ∷ Γ
| CVScope_Val : forall Γ C,
    VVCTX Γh ⊢ C ∷ Γ -> 
    EVCTX Γh ⊢ C ∷ Γ
with VVCtxScope (Γh : Env) : Env -> Ctx -> Prop :=
| CVScope_hole : VVCTX Γh ⊢ Ctx_hole ∷ Γh 
| CVScope_Fun : forall Γ C,
    EVCTX Γh ⊢ C ∷ (S Γ) ->
    VVCTX Γh ⊢ Ctx_Fun C ∷ Γ
where
"'EVCTX' Γh ⊢ C ∷ Γ" := (EVCtxScope Γh Γ C)
and
"'VVCTX' Γh ⊢ C ∷ Γ" := (VVCtxScope Γh Γ C).

Lemma plug_preserves_scope_val : forall {Γh C Γ e},
    (EVCTX Γh ⊢ C ∷ Γ ->
     VAL Γh ⊢ e ->
     EXP Γ ⊢ plug C e) /\
    (VVCTX Γh ⊢ C ∷ Γ ->
     VAL Γh ⊢ e ->
     VAL Γ ⊢ plug C e).
Proof.
  induction C;
    split;
    intros;
    inversion H; subst;
    cbn;
    try solve_inversion;
    auto;
    constructor;
    firstorder idtac.
  - inversion H1; subst. auto.
  - inversion H1; subst.
    constructor.
    firstorder idtac.
Qed.

Lemma plugc_preserves_scope_val : forall {Γh Couter Γ Cinner Γ'},
    (EVCTX Γ' ⊢ Couter ∷ Γ ->
     VVCTX Γh ⊢ Cinner ∷ Γ' ->
     EVCTX Γh ⊢ plugc Couter Cinner ∷ Γ) /\
    (VVCTX Γ' ⊢ Couter ∷ Γ ->
     VVCTX Γh ⊢ Cinner ∷ Γ' ->
     VVCTX Γh ⊢ plugc Couter Cinner ∷ Γ).
Proof.
  induction Couter;
    split;
    intros;
    inversion H; subst;
    cbn;
    try solve_inversion;
    auto;
    constructor;
    firstorder idtac.
  - inversion H1; subst.
    auto.
  - constructor.
    inversion H1; subst.
    firstorder idtac.
Qed.

Definition CTX (Γ : Env) (e1 e2 : Expr) :=
  (EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
  (forall (C : Ctx) A,
      EECTX Γ ⊢ C ∷ 0 ->
      Rbar_le (μeval_star (plug C e1) Knil A)
              (μeval_star (plug C e2) Knil A)).

Lemma CTX_bigger : forall R' : Env -> Expr -> Expr -> Prop,
    IsPreCtxRel R' -> forall (Γ : Env) (e1 e2 : Expr), R' Γ e1 e2 -> CTX Γ e1 e2.
Proof.
  intros R' HR.
  destruct HR as [Rscope [Radequate [Rrefl [Rtrans [RFun [RApp [ROp1 [ROp2 [RCond [RSeq RFactor]]]]]]]]]].
  unfold CTX.
  intros.
  destruct (Rscope _ _ _ H) as [Hscope_e1 Hscope_e2].
  intuition idtac;
    try solve [apply Rscope in H; intuition idtac];
    apply Radequate.
  assert (forall Γ', EECTX Γ ⊢ C ∷ Γ' -> 
                     R' Γ' (plug C e1) (plug C e2)).
  { clear H0.
    induction C;
      intros;
      inversion H0;
      subst;
      cbn;
      try solve_inversion;
      auto.
    - apply RFun.
      apply IHC.
      inversion H1; auto.
    - apply RApp; auto.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
      + apply IHC.
        constructor.
        auto.
    - apply RApp; auto.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
      + apply IHC.
        constructor.
        auto.
    - apply ROp1; auto.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
      + apply IHC.
        inversion H0; subst; try solve_inversion; auto.
        constructor.
        auto.
    - apply ROp2; auto.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
      + apply IHC.
        inversion H0; subst; try solve_inversion; auto.
        constructor.
        auto.
    - apply ROp2; auto.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
      + apply IHC.
        inversion H0; subst; try solve_inversion; auto.
        constructor.
        auto.
    - apply RCond; auto.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
      + apply IHC.
        inversion H0; subst; try solve_inversion; auto.
        constructor.
        auto.
    - apply RCond; auto.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
    - apply RCond; auto.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
      + eapply plug_preserves_scope_exp in H0; eauto 2.
  }
  apply H1.
  auto.
Qed.

Lemma use_Seq_instead : forall Γ e v C A,
    EXP S Γ ⊢ e ->
    VAL Γ ⊢ v ->
    EECTX Γ ⊢ C ∷ 0 ->
    μeval_star (plug C (Seq v e)) Knil A =
    μeval_star (plug C e.[v/]) Knil A.
Proof.
  intros.
  pose proof CTX_bigger.
  unfold CTX in H1.
  apply Rbar_le_antisym.
  { eapply H2 with (R':=CIU_open); eauto using CIU_IsPreCtxRel.
    unfold CIU_open.
    intros.
    asimpl.
    unfold CIU.
    intuition auto.
    - constructor.
      + constructor.
        apply -> sub_preserves_scope_val; eauto.
      + apply -> sub_preserves_scope_exp; eauto.
    - apply -> sub_preserves_scope_exp.
      + eauto.
      + apply cons_scope; auto.
        apply -> sub_preserves_scope_val; eauto.
    - run_μeval_star_for 1.
      erewrite μeval_star_step_1; revgoals.
      intros.
      rewrite μeval_step_Return.
      asimpl.
      reflexivity.
      apply -> sub_preserves_scope_val; eauto.
      apply Rbar_le_refl.
  }
  { eapply H2 with (R':=CIU_open); eauto using CIU_IsPreCtxRel.
    unfold CIU_open.
    intros.
    asimpl.
    unfold CIU.
    intuition auto.
    - apply -> sub_preserves_scope_exp.
      + eauto.
      + apply cons_scope; auto.
        apply -> sub_preserves_scope_val; eauto.
    - constructor.
      constructor.
      + apply -> sub_preserves_scope_val; eauto.
      + apply -> sub_preserves_scope_exp; eauto.
    - remember (μeval_star e.[v.[γ] .: γ] K).
      run_μeval_star_for 1.
      erewrite μeval_star_step_1; revgoals.
      intros.
      rewrite μeval_step_Return.
      asimpl.
      reflexivity.
      apply -> sub_preserves_scope_val; eauto.
      subst.
      apply Rbar_le_refl.
  }
Qed.

Lemma CTX_IsPreCtxRel : IsPreCtxRel CTX.
Proof.
  unfold IsPreCtxRel.
  intuition idtac;
    try solve
        [unfold CTX in H; intuition idtac
        |inversion H; [|constructor]; apply H0].
  - unfold Adequate.
    intros.
    unfold CTX in H.
    intuition idtac.
    + apply (H1 Ctx_hole).
      constructor.
  - unfold IsReflexive.
    intros.
    unfold CTX.
    intuition (auto using Rbar_le_refl).
  - unfold Transitive.
    intros.
    unfold CTX in *.
    intuition idtac.
    eapply Rbar_le_trans; firstorder.
  - unfold CompatibleFun.
    intros.
    unfold CTX in *.
    intuition auto.
    specialize (H1 (plugc C (Ctx_Fun Ctx_hole)) A).
    repeat rewrite <- plug_assoc in H1.
    cbn in H1.
    apply H1.
    eapply plugc_preserves_scope_exp; eauto.
    repeat constructor.
  - unfold CompatibleApp.
    intros.
    unfold CTX in *.
    intuition auto.
    assert (EECTX Γ ⊢ plugc C (Ctx_Seq_x Ctx_hole (App (Var 0) (rename (+1) v1))) ∷ 0).
    { eapply plugc_preserves_scope_exp; eauto.
      constructor.
      constructor.
      constructor.
      constructor.
      auto.
      apply -> ren_preserves_scope_val; eauto.
      unfold RenScoped.
      intros; asimpl; auto.
    }
    specialize (H6 _ A H10).
    repeat rewrite <- plug_assoc in H6.
    cbn in H6.
    assert (forall f1 v1,
               VAL Γ ⊢ f1 ->
               VAL Γ ⊢ v1 ->
               (μeval_star (plug C (App f1 v1)) Knil A =
                μeval_star (plug C (Seq f1 (App (Var 0) (rename (+1) v1)))) Knil A))
      as HApp_Seq_f.
    { intros.
      erewrite use_Seq_instead; eauto 2.
      asimpl.
      reflexivity.
      constructor; auto.
      apply -> ren_preserves_scope_val; eauto.
      unfold RenScoped.
      intros; cbn; auto.
    }
    assert (forall f1 v1,
               VAL Γ ⊢ f1 ->
               VAL Γ ⊢ v1 ->
               (μeval_star (plug C (App f1 v1)) Knil A =
                μeval_star (plug C (Seq v1 (App (rename (+1) f1) (Var 0)))) Knil A))
      as HApp_Seq_v.
    { intros.
      erewrite use_Seq_instead; eauto 2.
      asimpl.
      reflexivity.
      constructor; auto.
      apply -> ren_preserves_scope_val; eauto.
      unfold RenScoped.
      intros; cbn; auto.
    }
    rewrite HApp_Seq_f; auto.
    eapply Rbar_le_trans.
    apply H6.
    assert (EECTX Γ ⊢ plugc C (Ctx_Seq_x Ctx_hole (App (rename (+1) f2) (Var 0))) ∷ 0).
    { eapply plugc_preserves_scope_exp; eauto.
      constructor.
      constructor.
      constructor.
      - apply -> ren_preserves_scope_val; eauto.
        unfold RenScoped.
        intros; asimpl; auto.
      - constructor.
        auto.
    }
    specialize (H7 _ A H11).
    repeat rewrite <- plug_assoc in H7.
    rewrite HApp_Seq_v; auto.
    eapply Rbar_le_trans; revgoals.
    cbn in H7.
    apply H7.
    rewrite <- HApp_Seq_v; auto.
    rewrite <- HApp_Seq_f; auto.
  - unfold CompatibleOp1.
    intros.
    unfold CTX in *.
    intuition auto.
    assert (EECTX Γ ⊢ plugc C (Ctx_Seq_x Ctx_hole (Op1 o (Var 0))) ∷ 0).
    { eapply plugc_preserves_scope_exp; eauto.
      constructor.
      constructor.
      constructor.
      constructor.
      auto.
    }
    specialize (H3 _ A H5).
    repeat rewrite <- plug_assoc in H3.
    cbn in H3.
    assert (forall v1,
               VAL Γ ⊢ v1 ->
               (μeval_star (plug C (Op1 o v1)) Knil A =
                μeval_star (plug C (Seq v1 (Op1 o (Var 0)))) Knil A))
      as HApp_Op1.
    { intros.
      erewrite use_Seq_instead; eauto 2.
      constructor.
      auto.
    }
    rewrite HApp_Op1; auto.
    eapply Rbar_le_trans.
    apply H3.
    rewrite HApp_Op1; auto.
  - unfold CompatibleOp2.
    intros.
    unfold CTX in *.
    intuition auto.
    assert (EECTX Γ ⊢ plugc C (Ctx_Seq_x Ctx_hole (Op2 o (Var 0) (rename (+1) v1'))) ∷ 0).
    { eapply plugc_preserves_scope_exp;
        eauto;
        repeat (constructor; auto 1).
      apply -> ren_preserves_scope_val;
        eauto.
      unfold RenScoped.
      cbn.
      auto.
    }
    specialize (H6 _ A H10).
    repeat rewrite <- plug_assoc in H6.
    cbn in H6.
    assert (forall v1,
               VAL Γ ⊢ v1 ->
               (μeval_star (plug C (Op2 o v1 v1')) Knil A =
                μeval_star (plug C (Seq v1 (Op2 o (Var 0) (rename (+1) v1')))) Knil A))
      as HApp_Op2_1.
    { intros.
      erewrite use_Seq_instead; eauto 2.
      asimpl.
      auto.
      constructor.
      - auto.
      - apply -> ren_preserves_scope_val; eauto.
        unfold RenScoped.
        cbn.
        auto.
    }
    assert (forall v1',
               VAL Γ ⊢ v1' ->
               (μeval_star (plug C (Op2 o v2 v1')) Knil A =
                μeval_star (plug C (Seq v1' (Op2 o (rename (+1) v2) (Var 0)))) Knil A))
      as HApp_Op2_2.
    { intros.
      erewrite use_Seq_instead; eauto 2.
      asimpl.
      auto.
      constructor.
      - apply -> ren_preserves_scope_val; eauto.
        unfold RenScoped.
        cbn.
        auto.
      - auto.
    }
    rewrite HApp_Op2_1; auto.
    eapply Rbar_le_trans.
    apply H6.
    assert (EECTX Γ ⊢ plugc C (Ctx_Seq_x Ctx_hole (Op2 o (rename (+1) v2) (Var 0))) ∷ 0).
    { eapply plugc_preserves_scope_exp; eauto.
      constructor.
      constructor.
      constructor.
      - apply -> ren_preserves_scope_val; eauto.
        unfold RenScoped.
        intros; asimpl; auto.
      - constructor.
        auto.
    }
    specialize (H7 _ A H11).
    repeat rewrite <- plug_assoc in H7.
    rewrite HApp_Op2_2; auto.
    eapply Rbar_le_trans; revgoals.
    cbn in H7.
    apply H7.
    rewrite <- HApp_Op2_2; auto.
    rewrite <- HApp_Op2_1; auto.
  - unfold CompatibleCond.
    intros.
    unfold CTX in *.
    intuition auto.
    assert (EECTX Γ ⊢ plugc C (Ctx_Cond_t v1 Ctx_hole ef1) ∷ 0) as HCtx_t.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    assert (EECTX Γ ⊢ plugc C (Ctx_Cond_f v1 et2 Ctx_hole) ∷ 0) as HCtx_f.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    specialize (H10 _ A HCtx_t).
    repeat rewrite <- plug_assoc in H10.
    cbn in H10.
    eapply Rbar_le_trans.
    apply H10.
    specialize (H11 _ A HCtx_f).
    repeat rewrite <- plug_assoc in H11.
    cbn in H11.
    eapply Rbar_le_trans.
    apply H11.
    assert (EECTX Γ ⊢ plugc C (Ctx_Seq_x Ctx_hole (Cond (Var 0) (rename (+1) et2) (rename (+1) ef2))) ∷ 0) as HCtx_p.
    { eapply plugc_preserves_scope_exp;
        eauto.
      constructor.
      constructor.
      constructor.
      + constructor.
        auto.
      + apply -> ren_preserves_scope_exp;
          eauto.
        unfold RenScoped.
        cbn.
        auto 1.
      + apply -> ren_preserves_scope_exp;
          eauto.
        unfold RenScoped.
        cbn.
        auto 1.
    }
    specialize (H9 _ A HCtx_p).
    repeat rewrite <- plug_assoc in H9.
    cbn in H9.
    assert (forall vp,
               VAL Γ ⊢ vp ->
               (μeval_star (plug C (Cond vp et2 ef2)) Knil A =
                μeval_star (plug C (Seq vp (Cond (Var 0) (rename (+1) et2) (rename (+1) ef2)))) Knil A))
      as HSeq_Cond_p.
    { intros.
      erewrite use_Seq_instead; eauto 2.
      asimpl.
      auto.
      constructor.
      - auto.
      - apply -> ren_preserves_scope_exp; eauto.
        unfold RenScoped.
        cbn.
        auto 1.
      - apply -> ren_preserves_scope_exp; eauto.
        unfold RenScoped.
        cbn.
        auto 1.
    }
    rewrite HSeq_Cond_p; auto.
    eapply Rbar_le_trans.
    apply H9.
    rewrite <- HSeq_Cond_p; auto.
  - unfold CompatibleSeq.
    intros.
    unfold CTX in *.
    intuition auto.
    assert (EECTX Γ ⊢ (plugc C (Ctx_Seq_x Ctx_hole b1)) ∷ 0).
    { eapply plugc_preserves_scope_exp; eauto.
      constructor.
      constructor.
      auto.
    }
    specialize (H2 _ A H6).
    repeat rewrite <- plug_assoc in H2.
    cbn in H2.
    eapply Rbar_le_trans.
    eapply H2.
    assert (EECTX S Γ ⊢ (plugc C (Ctx_Seq_b x2 Ctx_hole)) ∷ 0).
    { eapply plugc_preserves_scope_exp; eauto.
      constructor.
      auto.
      constructor.
    }
    specialize (H3 _ A H7).
    repeat rewrite <- plug_assoc in H3.
    cbn in H3.
    apply H3.
  - unfold CompatibleFactor.
    intros.
    unfold CTX in *.
    intuition auto.
    assert (EECTX Γ ⊢ (plugc C (Ctx_Seq_x Ctx_hole (Factor (Var 0)))) ∷ 0).
    { eapply plugc_preserves_scope_exp; eauto.
      constructor.
      constructor.
      auto.
    }
    specialize (H3 _ A H5).
    repeat rewrite <- plug_assoc in H3.
    cbn in H3.
    assert (forall v1,
               VAL Γ ⊢ v1 ->
               (μeval_star (plug C (Factor v1)) Knil A =
                μeval_star (plug C (Seq v1 (Factor (Var 0)))) Knil A))
      as HFactor_Seq.
    { intros.
      erewrite use_Seq_instead; eauto 2.
      auto.
    }
    rewrite HFactor_Seq; auto.
    rewrite HFactor_Seq; auto.
Qed.    

Lemma CTX_IsCtxRel : IsCtxRel CTX.
Proof.
  unfold IsCtxRel.
  split.
  - apply CTX_IsPreCtxRel.
  - intros.
    eapply CTX_bigger; eauto.
Qed.

Lemma exists_CTX : exists R, IsCtxRel R.
Proof.
  exists CTX.
  apply CTX_IsCtxRel.
Qed.
    
(*** End Concrete CTX *)

Theorem CIU_IsCtxRel : IsCtxRel CIU_open.
Proof.
  destruct exists_CTX as [R' HR'].
  eapply bigger_implies_IsCtxRel; eauto using CIU_IsPreCtxRel.
  induction Γ; revgoals.
  - unfold CIU_open.
    intros.
    replace e1.[γ] with e1.[γ 0/].[(+1) >>> γ]; revgoals.
    { asimpl.
      replace (γ 0).[_] with (γ 0).
      autosubst.
      replace ((+1) >>> γ) with (upn 0 ((+1) >>> γ)) by auto.
      rewrite vscoped_ignores_sub;
        auto.
    }
    replace e2.[γ] with e2.[γ 0/].[(+1) >>> γ]; revgoals.
    { asimpl.
      replace (γ 0).[_] with (γ 0).
      autosubst.
      replace ((+1) >>> γ) with (upn 0 ((+1) >>> γ)) by auto.
      rewrite vscoped_ignores_sub;
        auto.
    }
    apply IHΓ.
    apply CTX_closed_under_substitution; auto; revgoals.
    + replace (γ 0) with (Var 0).[γ] by autosubst.
      apply sub_preserves_scope_val with (Γ:=S Γ); auto.
      unfold SubScoped in *.
      intros.
      apply H0 in H1.
      { clear R' HR' IHΓ e1 e2 H H0.
        induction Γ; auto.
        apply succ_ValScoped.
        auto.
      }
    + unfold SubScoped.
      cbn.
      intros.
      apply H0.
      auto.
  - unfold CIU_open.
    intros.
    unfold CIU.
    intuition idtac.
    + apply -> sub_preserves_scope_exp; eauto 3.
      eapply HR' with (e1:=e1) (e2:=e2); eauto 3.
    + apply -> sub_preserves_scope_exp; eauto 3.
      eapply HR' with (e1:=e1) (e2:=e2); eauto 3.
    + replace e1.[γ] with e1; revgoals.
      { replace γ with (upn 0 γ) by auto.
        rewrite escoped_ignores_sub; auto.
        eapply HR' with (e1:=e1) (e2:=e2); eauto.
      }
      replace e2.[γ] with e2; revgoals.
      { replace γ with (upn 0 γ) by auto.
        rewrite escoped_ignores_sub; auto.
        eapply HR' with (e1:=e1) (e2:=e2); eauto.
      }
      clear H0.
      revert K e1 e2 H1 H.
      induction K; intros.
      * apply HR'.
        auto.
      * replace (μeval_star e1 _ _)
          with (μeval_star (Seq e1 e) K A);
          revgoals.
        {
          run_μeval_star_for 1.
          auto.
        }
        replace (μeval_star e2 _ A)
          with (μeval_star (Seq e2 e) K A);
          revgoals.
        { run_μeval_star_for 1.
          auto.
        }
        inversion H1; subst.
        apply IHK; auto.
        apply HR'; auto.
        apply HR'; auto.
Qed.

Theorem Erel_IsCtxRel : IsCtxRel Erel_open.
Proof.
  unfold IsCtxRel.
  split.
  apply Erel_IsPreCtxRel.
  intros.
  apply CIU_iff_Erel.
  pose proof CIU_IsCtxRel.
  unfold IsCtxRel in H1.
  destruct H1.
  eapply H2; eauto.
Qed.
