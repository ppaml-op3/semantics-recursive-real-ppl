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

Set Bullet Behavior "Strict Subproofs".

Open Scope nat.

(* The Logical Relations *)
Definition Krel'
           (n : nat)
           (Vrel : forall m, m <= n -> Expr -> Expr -> Prop)
           (K1 K2 : Kont) : Prop :=
  KCLOSED K1 /\ KCLOSED K2 /\
  forall m (Hmn : m <= n) v1 v2,
    Vrel m Hmn v1 v2 ->
    Rbar_le (μeval m v1 K1) (μeval_star v2 K2).

Definition Erel'
           (n : nat)
           (Vrel : forall m, m <= n -> Expr -> Expr -> Prop)
           (e1 e2 : Expr) : Prop :=
  ECLOSED e1 /\ ECLOSED e2 /\
  forall m (Hmn : m <= n) K1 K2,
    Krel' m (fun m' H => Vrel m' (le_trans _ _ _ H Hmn)) K1 K2 ->
    Rbar_le (μeval m e1 K1) (μeval_star e2 K2).

Definition Vrel_rec
           (n : nat)
           (Vrel : forall m, m < n -> Expr -> Expr -> Prop)
           (v1 v2 : Expr) :=
  VCLOSED v1 /\ VCLOSED v2 /\
  match v1, v2 with
  | Const r1, Const r2 => r1 = r2
  | Fun b1, Fun b2 =>
    forall m (Hmn : (m < n)%nat),
    forall (v1' v2' : Expr),
      Vrel m Hmn v1' v2' ->
      Erel' m (fun m' H => Vrel m' (le_lt_trans _ _ _ H Hmn)) (b1.[v1'/]) (b2.[v2'/])
  | _,_ => False
  end.

Definition Vrel : nat -> Expr -> Expr -> Prop :=
  Fix lt_wf _ Vrel_rec.

Arguments Vrel n v1 v2 : simpl never.

Definition Erel (n : nat) (e1 e2 : Expr) : Prop :=
  Erel' n (fun m _ => Vrel m) e1 e2.

Arguments Erel n e1 e2 : simpl never.

Definition Krel (n : nat) (K1 K2 : Kont) : Prop :=
  Krel' n (fun m _ => Vrel m) K1 K2.

Arguments Krel n K1 K2 : simpl never.

Hint Extern 1 =>
match goal with
| [ |- context[Krel' ?m ?H ?K1 ?K2]] =>
  change (Krel' m H K1 K2) with (Krel m K1 K2)
| [ H : context[Krel' ?m ?H ?K1 ?K2] |- _] =>
  change (Krel' m H K1 K2) with (Krel m K1 K2) in H
| [ |- context[Erel' ?m ?H ?e1 ?e2]] =>
  change (Erel' m H e1 e2) with (Erel m e1 e2)
| [ H : context[Erel' ?m ?H ?e1 ?e2] |- _] =>
  change (Erel' m H e1 e2) with (Erel m e1 e2) in H
end.

Definition Grel (n : nat) (Γ : Env) (γ1 γ2 : var -> Expr) :=
  SUBSCOPE Γ ⊢ γ1 ∷ 0 /\
  SUBSCOPE Γ ⊢ γ2 ∷ 0 /\
  forall (x : var),
    x < Γ ->
    Vrel n (γ1 x) (γ2 x).

Definition Vrel_open (Γ : Env) (e1 e2 : Expr) :=
  forall n γ1 γ2,
    Grel n Γ γ1 γ2 ->
    Vrel n e1.[γ1] e2.[γ2].

Definition Erel_open (Γ : Env) (e1 e2 : Expr) :=
  forall n γ1 γ2,
    Grel n Γ γ1 γ2 ->
    Erel n e1.[γ1] e2.[γ2].

(* This is needed for unfolding the rec. *)
Lemma Vrel_rec_pointwise {n : nat} :
  forall (f g : forall m : nat, (m < n)%nat -> Expr -> Expr -> Prop),
    (forall (m : nat) (p : (m < n)%nat), f m p = g m p) ->
    Vrel_rec n f = Vrel_rec n g.
Proof.
  intros.
  unfold Vrel_rec.
  extensionality v1.
  extensionality v2.
  destruct v1, v2; auto.
  f_equal.
  f_equal.
  extensionality m.
  extensionality Hmn.
  extensionality v1'.
  extensionality v2'.
  rewrite H.
  extensionality x.
  f_equal.
  extensionality m'.
  extensionality H0.
  trivial.
Qed.

Lemma Vrel_Fix_eq : forall {n : nat} {v1 v2 : Expr},
    Vrel n v1 v2
    = 
    Vrel_rec n (fun (m : nat) (_ : m < n) => Vrel m) v1 v2.
Proof.
  intros.
  unfold Vrel.
  rewrite Fix_eq by (auto using Vrel_rec_pointwise).
  trivial.
Qed.

(** Section 4 note about V_n ⊆ V_{n+1}. *)

(* Vrel n can be smaller. *)
Lemma Vrel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {v1 v2 : Expr},
    Vrel n v1 v2 ->
    Vrel m v1 v2.
Proof.
  induction 1 using le_dep_ind;
    intros;
    eauto.
  rewrite Vrel_Fix_eq.
  rewrite Vrel_Fix_eq in H.
  unfold Vrel_rec at 1.
  unfold Vrel_rec at 1 in H.
  destruct v1, v2;
    intuition.
Qed.

Hint Resolve Vrel_downclosed.

Lemma Krel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {K1 K2 : Kont},
    Krel n K1 K2 ->
    Krel m K1 K2.
Proof.
  unfold Krel, Krel'.
  intuition.
Qed.

Hint Resolve Krel_downclosed.

Lemma Erel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {e1 e2 : Expr},
    Erel n e1 e2 ->
    Erel m e1 e2.
Proof.
  intros.
  unfold Erel, Erel'.
  unfold Erel, Erel' in H.
  intuition.
Qed.

Hint Resolve Erel_downclosed.

Lemma Grel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {Γ : Env} {γ1 γ2 : var -> Expr},
    Grel n Γ γ1 γ2 ->
    Grel m Γ γ1 γ2.
Proof.
  unfold Grel.
  intros.
  intuition (eauto using Vrel_downclosed).
Qed.

Hint Resolve Grel_downclosed.

Unset Printing Implicit.

Lemma Vrel_closed : forall {n : nat} {v1 v2 : Expr},
    Vrel n v1 v2 ->
    VCLOSED v1 /\ VCLOSED v2.
Proof.
  intros.
  destruct H as [? [? ?]].
  destruct v1, v2; intuition.
Qed.

Lemma Vrel_closed_l : forall {n : nat} {v1 v2 : Expr},
    Vrel n v1 v2 ->
    VCLOSED v1.
Proof.
  intros.
  apply Vrel_closed in H.
  intuition.
Qed.

Hint Resolve Vrel_closed_l.

Lemma Vrel_closed_r : forall {n : nat} {v1 v2 : Expr},
    Vrel n v1 v2 ->
    VCLOSED v2.
Proof.
  intros.
  apply Vrel_closed in H.
  intuition.
Qed.

Hint Resolve Vrel_closed_r.

Lemma Grel_cons : forall n Γ v1 v2 γ1 γ2,
    Grel n Γ γ1 γ2 ->
    Vrel n v1 v2 ->
    Grel n (S Γ) (v1 .: γ1) (v2 .: γ2).
Proof.
  intros.
  unfold Grel in *.
  intuition eauto.
  destruct x;
    eauto.
Qed.

Hint Resolve Grel_cons.

(* Automatically get rid of goals assuming variables are closed. *)
Hint Extern 5 =>
solve [match goal with
       | [H : VCLOSED Var _ |- _] =>
         exfalso;
           inversion H as [? B| | ];
           auto
       end].

Lemma Erel_closed : forall {n : nat} {e1 e2 : Expr},
    Erel n e1 e2 ->
    ECLOSED e1 /\ ECLOSED e2.
Proof.
  intros.
  unfold Erel, Erel' in H.
  intuition.
Qed.

Lemma Erel_closed_l : forall {n : nat} {e1 e2 : Expr},
    Erel n e1 e2 ->
    ECLOSED e1.
Proof.
  intros.
  apply Erel_closed in H.
  intuition.
Qed.

Hint Resolve Erel_closed_l.

Lemma Erel_closed_r : forall {n : nat} {e1 e2 : Expr},
    Erel n e1 e2 ->
    ECLOSED e2.
Proof.
  intros.
  apply Erel_closed in H.
  intuition.
Qed.

Hint Resolve Erel_closed_r.

Lemma Erel_open_closed : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    forall γ, SUBSCOPE Γ ⊢ γ ∷ 0 ->
              ECLOSED e1.[γ] /\ ECLOSED e2.[γ].
Proof.
  intros.
  apply @Erel_closed with (n:=0).
  apply H.
  unfold Grel.
  intuition idtac.
  rewrite Vrel_Fix_eq.
  unfold Vrel_rec at 1.
  destruct (H0 x); intuition.
Qed.

Lemma Erel_open_scope : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2.
Proof.
  intros.
  pose proof (Erel_open_closed H).
  split;
    eapply sub_implies_scope_exp;
    intros;
    apply H0; auto.
Qed.

Lemma Erel_open_scope_l : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    EXP Γ ⊢ e1.
Proof.
  intros.
  apply Erel_open_scope in H.
  intuition.
Qed.

Hint Resolve Erel_open_scope_l.

Lemma Erel_open_scope_r : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    EXP Γ ⊢ e2.
Proof.
  intros.
  apply Erel_open_scope in H.
  intuition.
Qed.

Hint Resolve Erel_open_scope_r.

Lemma Krel_closed : forall {n : nat} {K1 K2 : Kont},
    Krel n K1 K2 ->
    KCLOSED K1 /\ KCLOSED K2.
Proof.
  intros.
  unfold Krel, Krel' in H.
  intuition.
Qed.

Lemma Krel_closed_l : forall {n : nat} {K1 K2 : Kont},
    Krel n K1 K2 ->
    KCLOSED K1.
Proof.
  intros.
  apply Krel_closed in H.
  intuition.
Qed.

Hint Resolve Krel_closed_l.

Lemma Krel_closed_r : forall {n : nat} {K1 K2 : Kont},
    Krel n K1 K2 ->
    KCLOSED K2.
Proof.
  intros.
  apply Krel_closed in H.
  intuition.
Qed.

Hint Resolve Krel_closed_r.

Lemma Vrel_possibilities : forall {n} {v1 v2},
    Vrel n v1 v2 ->
    (exists r, v1 = Const r /\ v2 = Const r) \/
    (exists b1 b2, v1 = Fun b1 /\ v2 = Fun b2).
Proof.
  intros.
  destruct v1, v2;
    destruct H as [? [? ?]];
    subst;
    try contradiction;
    auto.
  - left.
    exists r0.
    intuition.
  - right.
    exists b, b0.
    intuition.
Qed.
