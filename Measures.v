Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Decidable.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Reals.Reals.
Require Import Coq.fourier.Fourier.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Lim_seq.
Set Bullet Behavior "Strict Subproofs".

Require Import Biorthogonality.Basics.

Local Hint Extern 9 =>
match goal with
| [ H : _ |- _ ] => solve [inversion H]
end.

Local Hint Extern 9 => contradiction.

Local Open Scope R.
Axiom Measurable : Type -> Type.
Axiom Measurable_R_eq_dec : forall (A1 A2 : Measurable R), decidable (A1 = A2).
Axiom Indicator : forall {A}, Measurable A -> A -> R.
Axiom Indicator_range : forall {A} (X : Measurable A) (x : A),
    Indicator X x = 0 \/ Indicator X x = 1.
Axiom Measurable_Singleton : R -> Measurable R.
Axiom Measurable_Singleton_Indicator_1 : forall r,
    Indicator (Measurable_Singleton r) r = 1.
Axiom Measurable_Singleton_Indicator_0 : forall r1 r2,
    r1 <> r2 ->
    Indicator (Measurable_Singleton r1) r2 = 0.
Axiom integrate : forall {A : Type}, (A -> Rbar) -> (Measurable A -> Rbar) -> Rbar.

(* Monotonicity is from Rudin, 11.23(c) *)
Axiom integrate_monotonic : forall {A : Type} (f g : A -> Rbar) (μ : Measurable A -> Rbar),
    (forall x, Rbar_le (f x) (g x)) ->
    Rbar_le (integrate f μ) (integrate g μ).

(* Linearity is from Rudin, 11.23(d) *)
Axiom integrate_linear : forall {A : Type} (c : R) (f : A -> Rbar) (μ : Measurable A -> Rbar),
    integrate (fun x => Rbar_mult c (f x)) μ = Rbar_mult c (integrate f μ).

Axiom Entropy : Set.
Axiom Entropy_π1 : Entropy -> Entropy.
Axiom Entropy_π2 : Entropy -> Entropy.
Axiom Entropy_eq_dec : forall (σ1 σ2 : Entropy), decidable (σ1 = σ2).

Axiom interpolate : Entropy -> Entropy -> Entropy.
Infix "#" := interpolate (at level 60).
Axiom interpolate_project_1 : forall σ1 σ2,
    Entropy_π1 (interpolate σ1 σ2) = σ1.
Axiom interpolate_project_2 : forall σ1 σ2,
    Entropy_π2 (interpolate σ1 σ2) = σ2.
Axiom interpolate_join : forall σ,
    interpolate (Entropy_π1 σ) (Entropy_π2 σ) = σ.
Axiom Entropy_extract : Entropy -> R.
Axiom μentropy : Measurable Entropy -> Rbar.
Axiom tonelli_μentropy : forall f,
  integrate (fun σ1 => integrate (fun σ2 => (f σ1 σ2)) μentropy) μentropy =
  integrate (fun σ2 => integrate (fun σ1 => (f σ1 σ2)) μentropy) μentropy.

(* Result of σ-finiteness of μentropy and the fact that μentropy of the whole
space is 1. *)
Axiom integrate_entropy_const :
  forall x, integrate (fun _ : Entropy => x) μentropy = x.
Lemma integrate_0 : integrate (fun _ => 0) μentropy = Finite 0.
Proof.
  rewrite integrate_entropy_const.
  auto.
Qed.

Axiom split_entropy : forall f,
    integrate (fun σ2 => integrate (fun σ1 => (f σ1 σ2)) μentropy) μentropy =
    integrate (fun σ => (f (Entropy_π1 σ) (Entropy_π2 σ))) μentropy.

Axiom lebesgue_monotone_convergence :
  forall A (f : nat -> A -> R) μ,
    (forall n x, Rbar_le (f n x) (f (S n) x)) ->
    Sup_seq (fun n => integrate (fun x => f n x) μ) =
    integrate (fun x => Lim_seq (fun n => f n x)) μ.

Instance integrate_Proper {A} : Proper (pointwise_relation A eq==>eq==>eq) integrate.
Proof.
  unfold Proper, respectful, pointwise_relation.
  intros.
  subst.
  f_equal.
  extensionality a.
  auto.
Qed.

Lemma Rbar_le_eq : forall x y, x = y -> Rbar_le x y.
Proof.
  intros.
  subst.
  apply Rbar_le_refl.
Qed.

Lemma Lim_seq_monotonic : forall (f : nat -> R),
    (forall n m, (n <= m)%nat -> f n <= f m) ->
    forall n, Rbar_le (f n) (Lim_seq f).
Proof.
  intros.
  rewrite <-Lim_seq_const at 1.
  apply Lim_seq_le_loc.
  unfold Hierarchy.eventually.
  exists n.
  intros.
  auto.
Qed.

Lemma Rbar_mult_Finite : forall x y,
    Finite (x * y) = Rbar_mult (Finite x) (Finite y).
Proof.
  auto.
Qed.

Lemma Sup_seq_incr_1 : forall u,
    (forall n, Rbar_le (u n) (u (S n))) ->
    Sup_seq u = Sup_seq (fun n => u (S n)).
Proof.
  intros u Hmon.
  apply Rbar_le_antisym.
  - apply Sup_seq_le.
    auto.
  - rewrite Rbar_sup_eq_lub.
    rewrite Rbar_sup_eq_lub.
    apply Lub.Rbar_lub_subset.
    firstorder.
Qed.

Local Open Scope nat.

Hint Resolve Rbar_le_refl.

Lemma monotonic_n : forall j u,
  (forall n, Rbar_le (u n) (u (S n))) ->
  forall n, Rbar_le (u n) (u (j + n)).
Proof.
  induction j;
    intros;
    auto.
  cbn.
  eapply Rbar_le_trans.
  apply H.
  specialize (IHj u H (S n)).
  replace (j + S n) with (S (j + n)) in IHj by auto.
  auto.
Qed.

Lemma Sup_seq_incr_n : forall j u,
    (forall n, Rbar_le (u n) (u (S n))) ->
    Sup_seq u = Sup_seq (fun n => u (j + n)).
Proof.
  intros.
  apply Rbar_le_antisym.
  - eauto using Sup_seq_le, monotonic_n.
  - rewrite Rbar_sup_eq_lub.
    rewrite Rbar_sup_eq_lub.
    apply Lub.Rbar_lub_subset.
    firstorder.
Qed.

Lemma Sup_seq_const : forall (M : Rbar),
    Sup_seq (fun n : nat => M) = M.
Proof.
  intros.
  apply is_sup_seq_unique.
  unfold is_sup_seq.
  destruct M; intros.
  - destruct eps; cbn.
    split; intros.
    + fourier.
    + exists 0%nat; fourier.
  - exists 0%nat.
    cbn.
    auto.
  - cbn.
    auto.
Qed.

Lemma Sup_seq_bounded :
  forall (u : nat -> Rbar) (M : Rbar),
    (forall n : nat, Rbar_le (u n) M) ->
    Rbar_le (Sup_seq (fun n : nat => u n)) M.
Proof.
  intros.
  rewrite <- Sup_seq_const.
  apply Sup_seq_le.
  auto.
Qed.

Instance Sup_seq_Proper_ext : Proper (pointwise_relation nat eq==>eq) Sup_seq.
Proof.
  unfold Proper, respectful, pointwise_relation.
  intros.
  apply Sup_seq_ext.
  auto.
Qed.

Lemma Sup_seq_minor_Rbar_le : forall (u : nat -> Rbar) (M : Rbar) (n : nat),
    Rbar_le M (u n) -> Rbar_le M (Sup_seq u).
Proof.
  intros.
  destruct M;
    eauto using Sup_seq_minor_le.
  remember (u n).
  destruct r; auto.
  rewrite <- Sup_seq_const at 1.
  rewrite Rbar_sup_eq_lub.
  rewrite Rbar_sup_eq_lub.
  apply Lub.Rbar_lub_subset.
  intros.
  destruct H0; subst.
  eauto.
Qed.
