Require Import Coq.Program.Program.
Require Import Coq.Program.Tactics.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Decidable.
Require Import Coq.Reals.Reals.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Lim_seq.
Require Import Autosubst.Autosubst.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.Logic.ProofIrrelevance.

Require Import Biorthogonality.Basics.
Require Import Biorthogonality.Measures.
Require Import Biorthogonality.Syntax.
Require Import Biorthogonality.OpSem.

Set Bullet Behavior "Strict Subproofs".

Open Scope R.

(*** From Evaluations to Measures. *)
(* Definition 5.1 *)
Definition μeval (n : nat) (e : Expr) (K : Kont) : Rbar :=
  integrate (fun σ2 => integrate (fun σ1 => eval n ⟨ σ1 | e | K | σ2 | 1 ⟩)
                                 μentropy)
            μentropy.

Definition μeval_star (e : Expr) (K : Kont) : Rbar :=
  integrate (fun σ2 => integrate (fun σ1 => eval_star ⟨ σ1 | e | K | σ2 | 1 ⟩)
                                 μentropy)
            μentropy.

Lemma μeval_nonnegative : forall m e K,
    Rbar_le 0 (μeval m e K).
Proof.
  intros.
  unfold μeval.
  replace (Finite 0)
    with (integrate (fun σ2 => (integrate (fun σ1 : Entropy => Rbar_mult (Finite 0) (eval m ⟨ σ1 | e | K | σ2 | 1 ⟩)) μentropy)) μentropy);
    cycle -1.
  { repeat setoid_rewrite integrate_linear.
    rewrite Rbar_mult_0_l.
    auto.
  }
  repeat (apply integrate_monotonic; intros).
  setoid_rewrite Rbar_mult_0_l.
  apply eval_weight_nonnegative.
  auto.
Qed.

Hint Resolve μeval_nonnegative.

Lemma μeval_star_nonnegative : forall e K,
    Rbar_le 0 (μeval_star e K).
Proof.
  intros.
  unfold μeval_star.
  replace (Finite 0)
    with (integrate (fun σ2 => integrate (fun σ1 : Entropy => Rbar_mult (Finite 0) (eval_star ⟨ σ1 | e | K | σ2 | 1 ⟩)) μentropy) μentropy).
  - repeat (apply integrate_monotonic; intros).
    unfold eval_star.
    rewrite Rbar_mult_0_l.
    rewrite <- Lim_seq_const.
    apply Lim_seq_le_loc.
    unfold Hierarchy.eventually.
    exists 0%nat.
    intros.
    apply eval_weight_nonnegative.
    auto.
  - setoid_rewrite Rbar_mult_0_l.
    setoid_rewrite integrate_0.
    setoid_rewrite integrate_0.
    auto.
Qed.

Hint Resolve μeval_star_nonnegative.

(* Lemma 5.3 part 3 *)
Lemma μeval_index_monotonic : forall (n m : nat) (Hmn: (m <= n)%nat) (e : Expr) (K : Kont),
    Rbar_le (μeval m e K) (μeval n e K).
Proof.
  intros.
  unfold μeval.
  repeat (eapply integrate_monotonic; intros).
  rename x into σ2.
  rename x0 into σ1.
  revert e K σ2 σ1.
  intros.
  apply eval_index_monotonic; auto.
Qed.

Hint Resolve μeval_index_monotonic.

(* Lemma 5.3 part 3 *)
Lemma μeval_star_index_monotonic : forall (n : nat) (e : Expr) (K : Kont),
    Rbar_le (μeval n e K) (μeval_star e K).
Proof.
  intros.
  unfold μeval, μeval_star.
  repeat (apply integrate_monotonic; intros).
  unfold eval_star.
  intros.
  apply (Lim_seq_monotonic (fun n => eval n ⟨ _ | e | K | _ | 1 ⟩)).
  intros.
  apply eval_index_monotonic; auto.
Qed.

Hint Resolve μeval_star_index_monotonic.

(* Lemma 5.4 part 4 (but using Lim_seq instead of Sup_seq) *)
Lemma μeval_lim_interchange : forall e K,
    μeval_star e K =
    Sup_seq (fun n => μeval n e K).
Proof.
  intros.
  unfold μeval, μeval_star.
  rewrite split_entropy.
  replace (Sup_seq _)
    with 
      (Sup_seq
         (fun n => integrate (fun σ => eval n ⟨ Entropy_π1 σ | e | K | Entropy_π2 σ | 1 ⟩)
                             μentropy));
    cycle -1.
  { f_equal.
    extensionality n.
    rewrite split_entropy.
    auto.
  }
  rewrite lebesgue_monotone_convergence;
    auto.
  intros.
  apply eval_index_monotonic_1.
  auto.
Qed.


(*** μeval step lemmas *)

(* Shows that all of the following lemmas apply to μeval_star as well. *)

Lemma μeval_0 : forall e K,
    μeval 0 e K = 0.
Proof.
  intros.
  unfold μeval.
  cbn.
  repeat rewrite integrate_0.
  auto.
Qed.

Lemma μeval_star_step_1 : forall {e1 e2 K1 K2},
    (forall n, μeval (S n) e1 K1 = μeval n e2 K2) ->
    μeval_star e1 K1 = μeval_star e2 K2.
Proof.
  intros.
  repeat rewrite μeval_lim_interchange.
  rewrite Sup_seq_incr_1 at 1; auto.
Qed.

Lemma μeval_star_step : forall j {e1 e2 K1 K2},
    (forall n, μeval (j + n) e1 K1 = μeval n e2 K2) ->
    μeval_star e1 K1 = μeval_star e2 K2.
Proof.
  intros.
  repeat rewrite μeval_lim_interchange.
  rewrite Sup_seq_incr_n with (j:=j) at 1; auto.
Qed.

Lemma μeval_star_step_end_1 : forall {e1 K1 r},
    (forall n, μeval (S n) e1 K1 = r) ->
    μeval_star e1 K1 = r.
Proof.
  intros.
  repeat rewrite μeval_lim_interchange.
  rewrite <- Sup_seq_const.
  rewrite Sup_seq_incr_1 at 1; auto.
Qed.

Lemma μeval_star_step_end : forall j {e1 K1 r},
    (forall n, μeval (j + n) e1 K1 = r) ->
    μeval_star e1 K1 = r.
Proof.
  intros.
  repeat rewrite μeval_lim_interchange.
  rewrite <- Sup_seq_const.
  rewrite Sup_seq_incr_n with (j:=j) at 1; auto.
Qed.

(* Lemma 5.4 {lemma-let} *)
Lemma μeval_step_Seq : forall {n e1 e2 K},
    μeval (S n) (Seq e1 e2) K = μeval n e1 (e2-:K).
Proof.
  intros.
  unfold μeval.
  setoid_rewrite eval_step_Seq.
  assert
    (forall σ2,
        integrate
          (fun σ1 =>
             eval n ⟨ Entropy_π1 σ1 | e1 | e2 -: K | Entropy_π2 σ1 # σ2 | 1 ⟩) μentropy
        =
        integrate
          (fun σ12 =>
             integrate
               (fun σ11 =>
                  eval n ⟨ σ11 | e1 | e2 -: K | σ12 # σ2 | 1 ⟩) μentropy) μentropy)
    by (setoid_rewrite split_entropy; auto).
  setoid_rewrite H.
  clear H.
  rewrite split_entropy.
  setoid_rewrite interpolate_join.
  auto.
Qed.

(* Lemma 5.5 {lemma-return} *)
Lemma μeval_step_Return : forall n v e K,
    VCLOSED v ->
    μeval (S n) v (e-:K) = μeval n e.[v/] K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite (eval_step_Return H).
  setoid_rewrite integrate_entropy_const.
  setoid_rewrite split_entropy.
  trivial.
Qed.

(* Lemma 5.6 {lemma-return} *)
Lemma μeval_step_App : forall n b v K,
    VCLOSED v ->
    μeval (S n) (App (Fun b) v) K = μeval n b.[v/] K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite eval_step_App.
  trivial.
Qed.

Lemma μeval_step_Op1_Exp : forall n r K,
    μeval (S n) (Op1 Exp (Const r)) K = μeval n (Const (Rexp r)) K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite eval_step_Op1_Exp.
  trivial.
Qed.

Lemma μeval_step_Op1_Log : forall {n r K},
    r <> 0 ->
    μeval (S n) (Op1 Log (Const r)) K =
    μeval n (Const (Rlog r)) K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite (eval_step_Op1_Log H).
  trivial.
Qed.

Lemma μeval_step_Op1_Log_0 : forall {n K},
    μeval (S n) (Op1 Log (Const 0)) K = 0.
Proof.
  unfold μeval.
  intros.
  unfold eval.
  unfold run.
  cbn.
  destruct Req_EM_T; try contradiction.
  repeat rewrite integrate_0.
  auto.
Qed.

Lemma μeval_step_Op1_Realp_1 : forall {n r K},
    μeval (S n) (Op1 Realp (Const r)) K =
    μeval n (Const 1%R) K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite eval_step_Op1_Realp_1.
  trivial.
Qed.

Lemma μeval_step_Op1_Realp_0 : forall {n b K},
    μeval (S n) (Op1 Realp (Fun b)) K =
    μeval n (Const 0%R) K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite eval_step_Op1_Realp_0.
  trivial.
Qed.

Lemma μeval_step_Op2_Plus : forall {n r1 r2 K},
    μeval (S n) (Op2 Plus (Const r1) (Const r2)) K =
    μeval n (Const (Rplus r1 r2)) K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite eval_step_Op2_Plus.
  trivial.
Qed.

Lemma μeval_step_Op2_Minus : forall {n r1 r2 K},
    μeval (S n) (Op2 Minus (Const r1) (Const r2)) K =
    μeval n (Const (Rminus r1 r2)) K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite eval_step_Op2_Minus.
  trivial.
Qed.

Lemma μeval_step_Op2_Times : forall {n r1 r2 K},
    μeval (S n) (Op2 Times (Const r1) (Const r2)) K =
    μeval n (Const (Rmult r1 r2)) K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite eval_step_Op2_Times.
  trivial.
Qed.

Lemma μeval_step_Op2_Div : forall {n r1 r2 K},
    r2 <> 0 ->
    μeval (S n) (Op2 Div (Const r1) (Const r2)) K =
    μeval n (Const (Rdiv r1 r2)) K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite (eval_step_Op2_Div H).
  trivial.
Qed.

Lemma μeval_step_Op2_Div_0 : forall {n r1 K},
    μeval (S n) (Op2 Div (Const r1) (Const 0)) K = 0.
Proof.
  unfold μeval.
  intros.
  unfold eval.
  unfold run.
  cbn.
  destruct Req_EM_T; try contradiction.
  repeat rewrite integrate_0.
  auto.
Qed.

Lemma μeval_step_Op2_Le_1 : forall {n r1 r2 K},
    r1 <= r2 ->
    μeval (S n) (Op2 Le (Const r1) (Const r2)) K =
    μeval n (Const 1%R) K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite (eval_step_Op2_Le_1 H).
  trivial.
Qed.

Lemma μeval_step_Op2_Le_0 : forall {n r1 r2 K},
    r2 < r1 ->
    μeval (S n) (Op2 Le (Const r1) (Const r2)) K =
    μeval n (Const 0%R) K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite (eval_step_Op2_Le_0 H).
  trivial.
Qed.

Lemma μeval_step_Op2_Lt_1 : forall {n r1 r2 K},
    r1 < r2 ->
    μeval (S n) (Op2 Lt (Const r1) (Const r2)) K =
    μeval n (Const 1%R) K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite (eval_step_Op2_Lt_1 H).
  trivial.
Qed.

Lemma μeval_step_Op2_Lt_0 : forall {n r1 r2 K},
    r2 <= r1 ->
    μeval (S n) (Op2 Lt (Const r1) (Const r2)) K =
    μeval n (Const 0%R) K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite (eval_step_Op2_Lt_0 H).
  trivial.
Qed.

Lemma μeval_step_Cond_true : forall {n r et ef K},
    0 < r ->
    μeval (S n) (Cond (Const r) et ef) K =
    μeval n et K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite (eval_step_Cond_true H).
  trivial.
Qed.

Lemma μeval_step_Cond_false : forall {n r et ef K},
    r <= 0 ->
    μeval (S n) (Cond (Const r) et ef) K =
    μeval n ef K.
Proof.
  unfold μeval.
  intros.
  setoid_rewrite (eval_step_Cond_false H).
  trivial.
Qed.

(* Lemma 5.7 *)
Lemma μeval_step_Sample : forall n K,
    μeval (S n) Sample K =
    integrate (fun σ => μeval n (Const (Entropy_extract σ)) K) μentropy.
Proof.
  intros.
  unfold μeval.
  setoid_rewrite eval_step_Sample.
  setoid_rewrite tonelli_μentropy at 2.
  setoid_rewrite split_entropy at 3.
  trivial.
Qed.

(* Lemma 5.7 *)
Lemma μeval_step_Factor : forall n r K,
    (0 <= r)%R ->
    μeval (S n) (Factor (Const r)) K =
    Rbar_mult r (μeval n (Const r) K).
Proof.
  intros.
  unfold μeval at 1.
  setoid_rewrite (eval_step_Factor H).
  setoid_rewrite Rbar_mult_Finite.
  setoid_rewrite <- integrate_linear.
  setoid_rewrite <- integrate_linear.
  trivial.
Qed.

Require Import Coq.Setoids.Setoid.

Lemma μeval_step_App_Const : forall n r e K,
    μeval n (App (Const r) e) K = 0%R.
Proof.
  intros.
  destruct n.
  - apply μeval_0.
  - unfold μeval.
    unfold eval.
    cbn.
    repeat rewrite integrate_entropy_const.
    trivial.
Qed.

Lemma μeval_step_Fun_Knil : forall m b A,
    μeval m (Fun b) (Knil A) = 0%R.
Proof.
  intros.
  unfold μeval.
  unfold eval.
  destruct m;
    cbn;
    repeat rewrite integrate_0;
    auto.
Qed.

Lemma μeval_step_Factor_Fun : forall b n K,
    μeval n (Factor (Fun b)) K = 0%R.
Proof.
  intros.
  unfold μeval.
  destruct n;
    cbn;
    rewrite integrate_0;
    rewrite integrate_0;
    auto.
Qed.

Set Printing Coercions.

Lemma μeval_star_step_Sample: forall K : Kont,
    μeval_star Sample K =
    integrate (fun σ : Entropy => μeval_star (Const (Entropy_extract σ)) K) μentropy.
Proof.
  intros K.
  unfold μeval_star at 1.

  replace (fun σ2' => integrate (fun σ1' => eval_star _) μentropy)
    with (fun σ2' =>
            integrate
              (fun σ1' =>
                 eval_star ⟨ Entropy_π1 σ1' | Const (Entropy_extract (Entropy_π2 σ1')) | K | σ2' | 1 ⟩)
              μentropy);
    revgoals.
  { extensionality σ2'.
    f_equal.
    extensionality σ1'.
    unfold eval_star at 2.
    rewrite <- Lim_seq_incr_1.
    unfold eval_star at 1.
    auto.
  }

  replace (fun σ2' => integrate (fun σ1' => eval_star _) _)
    with (fun σ2' =>
            integrate (fun σ2 =>
                         integrate
                           (fun σ1 =>
                              eval_star ⟨σ1 | Const (Entropy_extract σ2) | K | σ2' | 1⟩)
                           μentropy)
                      μentropy)
    by (extensionality σ'; apply split_entropy).
  rewrite tonelli_μentropy.
  auto.
Qed.

Ltac run_μeval_1 :=
  match goal with
  | [ |- context[ μeval (S ?n) (App (Fun ?b) ?v) ?K ] ] =>
    setoid_replace (μeval (S n) (App (Fun b) v) K)
      with (μeval n b.[v/] K)
      by (apply μeval_step_App;
          auto)
  | [ |- context[ μeval (S ?n) (Seq ?e1 ?e2) ?K ] ] =>
    setoid_replace (μeval (S n) (Seq e1 e2) K)
      with (μeval n e1 (e2-:K))
      by (apply μeval_step_Seq)
  | [ |- context[ μeval (S ?n) Sample ?K ] ] =>
    setoid_replace (μeval (S n) Sample K)
      with (integrate (fun σ => μeval n (Const (Entropy_extract σ)) K) μentropy)
      by (apply μeval_step_Sample)
  | [ |- context[ μeval (S ?n) (Factor (Const ?r)) ?K ] ] =>
    setoid_replace (μeval (S n) (Factor (Const r)) K)
      with (Rbar_mult r (μeval n (Const r) K))
      by (apply μeval_step_Factor;
          destruct (Rle_dec 0 r);
          auto)
  | [ |- context[ μeval (S ?n) ?v (?e-:?K) ] ] =>
    setoid_replace (μeval (S n) v (e-:K))
      with (μeval n e.[v/] K)
      by (apply μeval_step_Return;
          auto)
  | [ |- context[ μeval 0 ?e ?K ] ] =>
    setoid_replace (μeval 0 e K)
      with 0%R
      by (apply μeval_0;
          auto)
  | [ |- context[ μeval ?n (App (Const ?r) ?v) ?K ] ] =>
    setoid_replace (μeval n (App (Const r) v) K)
      with 0%R
      by (apply μeval_step_App_Const)
  (* Op1 *)
  | [ |- context[ μeval ?n (Op1 Exp (Const ?r)) ?K ] ] =>
    setoid_replace (μeval n (Op1 Exp (Const r)) K)
      with (μeval n (Const (Rexp r)) K)
      by (apply μeval_step_Op1_Exp)
  | [ |- context[ μeval ?n (Op1 Log (Const ?r)) ?K ] ] =>
    setoid_replace (μeval n (Op1 Log (Const r)) K)
      with (μeval n (Const (Rlog r)) K)
      by (apply μeval_step_Op1_Log)
  | [ |- context[ μeval ?n (Op1 Realp (Const ?r)) ?K ] ] =>
    setoid_replace (μeval n (Op1 Realp (Const r)) K)
      with (μeval n (Const 1%R) K)
      by (apply μeval_step_Op1_Realp_1)
  | [ |- context[ μeval ?n (Op1 Realp (Fun ?b)) ?K ] ] =>
    setoid_replace (μeval n (Op1 Realp (Fun ?b)) K)
      with (μeval n (Const 0%R) K)
      by (apply μeval_step_Op1_Realp_0)
  (* Op2 *)
  | [ |- context[ μeval ?n (Op2 Plus (Const ?r1) (Const ?r2)) ?K ] ] =>
    setoid_replace (μeval n (Op2 Plus (Const r1) (Const r2)) K)
      with (μeval n (Const (Rplus r1 r2)) K)
      by (apply μeval_step_Op2_Plus)
  | [ |- context[ μeval ?n (Op2 Minus (Const ?r1) (Const ?r2)) ?K ] ] =>
    setoid_replace (μeval n (Op2 Minus (Const r1) (Const r2)) K)
      with (μeval n (Const (Rminus r1 r2)) K)
      by (apply μeval_step_Op2_Minus)
  | [ |- context[ μeval ?n (Op2 Times (Const ?r1) (Const ?r2)) ?K ] ] =>
    setoid_replace (μeval n (Op2 Times (Const r1) (Const r2)) K)
      with (μeval n (Const (Rmult r1 r2)) K)
      by (apply μeval_step_Op2_Times)
  | [ |- context[ μeval ?n (Op2 Div (Const ?r1) (Const ?r2)) ?K ] ] =>
    setoid_replace (μeval n (Op2 Div (Const r1) (Const r2)) K)
      with (μeval n (Const (Rdiv r1 r2)) K)
      by (apply μeval_step_Op2_Div)
  (* Fun Knil *)
  | [ |- context[ μeval ?n (Fun ?b) (Knil ?A) ] ] =>
    setoid_replace (μeval n (Fun b) (Knil A))
      with 0%R
      by (apply μeval_step_Fun_Knil)
  (* Factor Fun *)
  | [ |- context[ μeval ?n (Factor (Fun ?b)) ?K ] ] =>
    setoid_replace (μeval n (Factor (Fun b)) K)
      with 0%R
      by (apply μeval_step_Factor_Fun)
  | _ => fail "no μeval found"
  end;
  asimpl.

Ltac run_μeval_H_1 H :=
  match goal with
  | [ H : context[ μeval (S ?n) (App (Fun ?b) ?v) ?K ] |- _ ] =>
    setoid_replace (μeval (S n) (App (Fun b) v) K)
      with (μeval n b.[v/] K)
      in H
      by (apply μeval_step_App;
          auto)
  | [ H : context[ μeval (S ?n) (Seq ?e1 ?e2) ?K ] |- _ ] =>
    setoid_replace (μeval (S n) (Seq e1 e2) K)
      with (μeval n e1 (e2-:K))
      in H
      by (apply μeval_step_Seq)
  | [ H : context[ μeval (S ?n) Sample ?K ] |- _ ] =>
    setoid_replace (μeval (S n) Sample K)
      with (integrate (fun σ => μeval n (Const (Entropy_extract σ)) K) μentropy)
      in H
      by (apply μeval_step_Sample)
  | [ H : context[ μeval (S ?n) (Factor (Const ?r)) ?K ] |- _ ] =>
    setoid_replace (μeval (S n) (Factor (Const r)) K)
      with (Rbar_mult r (μeval n (Const r) K))
      in H
      by (apply μeval_step_Factor;
          destruct (Rle_dec 0 r);
          auto)
  | [ H : context[ μeval (S ?n) ?v (?e-:?K) ] |- _ ] =>
    setoid_replace (μeval (S n) v (e-:K))
      with (μeval n e.[v/] K)
      in H
      by (apply μeval_step_Return;
          auto)
  | [ H : context[ μeval 0 ?e ?K ] |- _ ] =>
    setoid_replace (μeval 0 e K)
      with 0%R
      in H
      by (apply μeval_0;
          auto)
  | [ H : context[ μeval ?n (App (Const _) ?v) ?K ] |- _ ] =>
    setoid_replace (μeval n (App (Const _) v) K)
      with 0%R
      in H
      by (apply μeval_step_App_Const;
          auto)
  | [ |- context[ μeval ?n (Fun ?b) (Knil ?A) ] ] =>
    setoid_replace (μeval n (Fun b) (Knil A))
      with 0%R
      in H
      by (apply μeval_step_Fun_Knil)
  | [ |- context[ μeval ?n (Factor (Fun ?b)) ?K ] ] =>
    setoid_replace (μeval n (Factor (Fun b)) K)
      with 0%R
      in H
      by (apply μeval_step_Factor_Fun)
  | _ => fail "no μeval found"
  end;
  asimpl.

Ltac run_μeval := repeat run_μeval_1;
                  try (apply μeval_nonnegative + apply μeval_star_nonnegative).
Ltac run_μevalH H := repeat (run_μeval_H_1 H).

Tactic Notation "run_μeval" "in" ident(H) := run_μevalH H.
Tactic Notation "run_μeval" "in" "*" := in_all (run_μevalH); run_μeval.

Ltac run_μeval_for_helper n :=
  match n with
  | 0%nat => idtac
  | S ?n' =>
    match goal with
    | [ |- context[μeval ?m ?e ?K]] =>
      destruct m;
      [run_μeval; auto; try (apply μeval_nonnegative + apply μeval_star_nonnegative)
      |run_μeval_1; run_μeval_for_helper n'
      ]
    end
  end.

Ltac run_μeval_for n :=
  run_μeval_for_helper n;
  try (apply μeval_nonnegative + apply μeval_star_nonnegative).

Ltac run_μeval_star_for n :=
  first [erewrite (μeval_star_step n);
         [|cbn;
           intros;
           run_μeval;
           reflexivity]
        |erewrite (μeval_star_step_end n);
         [|cbn;
           intros;
           run_μeval;
           reflexivity]].

Lemma pure_steps_monotonic_μeval : forall e K e' K',
    (forall σ σK w, step ⟨ σ | e | K | σK | w ⟩ = Some ⟨ σ | e' | K' | σK | w ⟩) ->
    forall n, Rbar_le (μeval n e K) (μeval n e' K').
Proof.
  intros.
  unfold μeval.
  repeat (apply integrate_monotonic; intros).
  apply eval_step_monotonic.
  - auto using Rle_0_1.
  - destruct e; auto.
Qed.

Lemma pure_steps_preserve_μeval_star : forall e K e' K',
    (forall σ σK w, step ⟨ σ | e | K | σK | w ⟩ = Some ⟨ σ | e' | K' | σK | w ⟩) ->
    μeval_star e K = μeval_star e' K'.
Proof.
  intros.
  unfold μeval_star.
  f_equal.
  extensionality σ2.
  f_equal.
  extensionality σ1.
  unfold eval_star.
  rewrite <- Lim_seq_incr_1.
  f_equal.
  extensionality n.
  erewrite eval_step.
  - reflexivity.
  - apply H.
Qed.

Lemma pure_steps_preserve_μeval : forall n e K e' K',
    (forall σ σK w, step ⟨ σ | e | K | σK | w ⟩ = Some ⟨ σ | e' | K' | σK | w ⟩) ->
    μeval (S n) e K = μeval n e' K'.
Proof.
  intros.
  unfold μeval.
  f_equal.
  extensionality σ2.
  f_equal.
  extensionality σ1.
  erewrite eval_step.
  - reflexivity.
  - apply H.
Qed.

Local Open Scope nat.

Definition loop := (App (Fun (App (Var 0) (Var 0)))
                        (Fun (App (Var 0) (Var 0)))).

Lemma μeval_loop_0 : forall K n, μeval n loop K = 0%R.
Proof.
  induction n using lt_wf_ind; intros.
  destruct n as [|[|]];
    unfold loop;
    run_μeval;
    auto.
Qed.

Lemma μeval_star_loop_0 : forall K, μeval_star loop K = 0%R.
Proof.
  intros.
  rewrite μeval_lim_interchange.
  rewrite <- Sup_seq_const.
  apply Sup_seq_ext.
  apply μeval_loop_0.
Qed.
