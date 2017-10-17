Require Import Coq.Program.Program.
Require Import Coq.Program.Tactics.
Require Import Coquelicot.Coquelicot.
Set Bullet Behavior "Strict Subproofs".
Require Import Coq.omega.Omega.
Require Import Coq.fourier.Fourier.

Ltac solve_inversion :=
  match goal with
  | [ H : _ |- _ ] => solve [inversion H]
  end.

Local Hint Extern 9 => solve_inversion.

Local Hint Extern 9 => contradiction.

Scheme le_dep_ind := Induction for le Sort Prop.

Lemma le_pf_unique : forall (n m : nat) (H1 H2 : (n <= m)%nat),
    H1 = H2.
Proof.
  intros.
  induction H1 using le_dep_ind.
  - dependent destruction H2; auto.
    destruct (Nat.nle_succ_diag_l _ H2).
  - dependent destruction H2; auto.
    + destruct (Nat.nle_succ_diag_l _ H1).
    + erewrite IHle.
      f_equal.
Qed.

Lemma lt_pf_unique : forall (n m : nat) (H1 H2 : (n < m)%nat),
    H1 = H2.
Proof.
  intros.
  induction H1 using le_dep_ind.
  - dependent destruction H2; auto.
    destruct (Nat.nle_succ_diag_l _ H2).
  - dependent destruction H2; auto.
    + destruct (Nat.nle_succ_diag_l _ H1).
    + erewrite IHle.
      f_equal.
Qed.

Lemma Rbar_mult_le_compat_l : forall r r1 r2 : Rbar,
    Rbar_le (Finite 0) r ->
    Rbar_le r1 r2 ->
    Rbar_le (Rbar_mult r r1) (Rbar_mult r r2).
Proof.
  intros r r1 r2 H H0.
  destruct r; cbn in H;
    auto.
  - destruct r1, r2;
      cbn in *;
      auto;
      unfold Rbar_mult, Rbar_mult';
      try apply Rmult_le_compat_l;
      try fourier;
      refine (match H with
              | or_introl H1 => _
              | or_intror H1 => _
              end);
      destruct (Rle_dec 0 r);
      try match goal with
      | [ |- context[Rle_lt_or_eq_dec 0 ?r ?r1]] =>
        destruct (Rle_lt_or_eq_dec 0 r r1)
      end;
      subst;
      cbn;
      try fourier;
      auto.
  - destruct r1, r2;
      cbn;
      unfold Rbar_mult, Rbar_mult';
      repeat destruct Rle_dec;
      repeat destruct Rle_lt_or_eq_dec;
      subst;
      auto.
    + cbn in H0.
      fourier.
    + cbn in H0.
      exfalso.
      assert (0 <= r0) by fourier.
      apply n in H1.
      auto.
Qed.

Hint Extern 1 (_ = _)%nat => abstract omega.
Hint Extern 1 (_ <= _)%nat => abstract omega.
Hint Extern 1 (_ >= _)%nat => abstract omega.
Hint Extern 1 (_ < _)%nat => abstract omega.
Hint Extern 1 (_ > _)%nat => abstract omega.
Hint Extern 1 (_ <= _)%R => abstract fourier.
Hint Extern 1 (_ >= _)%R => abstract fourier.
Hint Extern 1 (_ < _)%R => abstract fourier.
Hint Extern 1 (_ > _)%R => abstract fourier.
Hint Extern 1 False => abstract omega.
Hint Extern 1 False => abstract fourier.
Hint Resolve Sup_seq_ext.
