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

Set Bullet Behavior "Strict Subproofs".

Local Hint Extern 9 => contradiction.
Local Hint Extern 9 => discriminate.

Open Scope R.

(*** Operational Semantics *)

Inductive UnweightedConfiguration : Type :=
| Configuration_done : UnweightedConfiguration
| Configuration_more : forall (σ : Entropy) (e : Expr) (K : Kont) (σK : Entropy),
    UnweightedConfiguration.

Inductive Configuration : Type :=
| mkConfiguration : forall (c : UnweightedConfiguration) (w : R),
    Configuration.

Notation "⟨ c | w ⟩" := (mkConfiguration c w).

Notation "⟨ σ | e | K | σK | w ⟩" := (⟨ Configuration_more σ e K σK | w ⟩).

Notation "⟨ r ⟩" := (mkConfiguration Configuration_done r).

Axiom Rexp : R -> R.
Axiom Rlog : R -> R.

Definition δ1 (o : EOp1) (v : Expr) : option Expr :=
  match o, v with
  | Exp, Const r => Some (Const (Rexp r))
  | Log, Const r =>
    match Req_EM_T 0 r with
    | in_left => None
    | in_right => Some (Const (Rlog r))
    end
  | Realp, Const _ => Some (Const 1%R)
  | Realp, Fun _ => Some (Const 0%R)
  | _, _ => None
  end.

Definition δ2 (o : EOp2) (v1 v2 : Expr) : option Expr :=
  match o, v1, v2 with
  | Plus, Const r1, Const r2 => Some (Const (Rplus r1 r2))
  | Minus, Const r1, Const r2 => Some (Const (Rminus r1 r2))
  | Times, Const r1, Const r2 => Some (Const (Rmult r1 r2))
  | Div, Const r1, Const r2 =>
    match Req_EM_T 0 r2 with
    | in_left => None
    | in_right => Some (Const (Rdiv r1 r2))
    end
  | Lt, Const r1, Const r2 =>
    match Rlt_dec r1 r2 with
    | in_left => Some (Const 1%R)
    | in_right => Some (Const 0%R)
    end
  | Le, Const r1, Const r2 =>
    match Rle_dec r1 r2 with
    | in_left => Some (Const 1%R)
    | in_right => Some (Const 0%R)
    end
  | _,_,_ => None
  end.

Definition step (c : Configuration) : option Configuration :=
  match c with
  | mkConfiguration Configuration_done r => None
  | mkConfiguration (Configuration_more σ e K σK) w =>
    match e with
    | Var x => None
    | Const r =>
      match K with
      | Knil A => Some ⟨ (Indicator A r) * w ⟩
      | e'-:K' => Some ⟨ Entropy_π1 σK | e'.[Const r/] | K' | Entropy_π2 σK | w ⟩
      end
    | Fun b =>
      match K with
      | Knil A => None
      | e'-:K' => Some ⟨ Entropy_π1 σK | e'.[Fun b/] | K' | Entropy_π2 σK | w ⟩
      end
    | App (Fun b) v => Some ⟨ σ | b.[v/] | K | σK | w ⟩
    | App _ _ => None
    | Seq x b => Some ⟨ Entropy_π1 σ | x | b-:K | (Entropy_π2 σ)#σK | w ⟩
    | Op1 o v =>
      match δ1 o v with
      | Some e' => Some ⟨ σ | e' | K | σK | w ⟩
      | None => None
      end
    | Op2 o v1 v2 =>
      match δ2 o v1 v2 with
      | Some e' => Some ⟨ σ | e' | K | σK | w ⟩
      | None => None
      end
    | Cond (Const r) et ef =>
      match Rlt_dec 0 r with
      | in_left => Some ⟨ σ | et | K | σK |w ⟩
      | in_right => Some ⟨ σ | ef | K | σK |w ⟩
      end
    | Cond _ _ _ => None
    | Sample => Some ⟨ Entropy_π1 σ | Const (Entropy_extract (Entropy_π2 σ)) | K | σK | w ⟩
    | Factor (Const r) =>
      match Rle_dec 0 r with
      | in_left => Some ⟨ σ | Const r | K | σK | w * r ⟩
      | in_right => None
      end
    | Factor _ => None
    end
  end.

Ltac solve_step e K H :=
  (* var *)
  let v := fresh "v" in
  (* const *)
  let r := fresh "r" in
  (* fun *)
  let b := fresh "b" in
  (* app *)
  let e1 := fresh "e1" in
  let e2 := fresh "e2" in
  (* seq *)
  let x := fresh "x" in
  let b := fresh "b" in
  (* op1 *)
  let o := fresh "o" in
  (* op2 *)
  let v1 := fresh "v1" in
  let v2 := fresh "v2" in
  (* cond *)
  let vp := fresh "vp" in
  let et := fresh "et" in
  let ef := fresh "ef" in
  (* factor *)
  let r := fresh "r" in
  destruct e as [v|r|b|e1 e2|x b|o v|o v1 v2|vp et ef| |r]; 
  [                             (* var *)
  |                             (* const *)
  |                             (* fun *)
  |                             (* app *)
  |                             (* seq *)
  |destruct o, v; auto             (* op1 *)
  |destruct o, v1, v2; auto            (* op2 *)
  |destruct vp; auto            (* cond *)
  |                             (* sample *)
  |destruct r; auto];           (* factor *)
  try solve
      [cbn in *;
       unfold δ1 in *;
       unfold δ2 in *;
       try destruct e1;
       try destruct Rle_dec;
       try destruct Rlt_dec;
       try destruct Req_EM_T;
       eauto;
       destruct K;
       cbn in *;
       inversion H;
       subst;
       eauto].

Lemma step_preserves_environment : forall {e1 σ1 K1 σK1 w1 σ2 e2 K2 σK2 w2},
    ECLOSED e1 ->
    KCLOSED K1 ->
    step ⟨σ1|e1|K1|σK1|w1⟩ = Some ⟨σ2|e2|K2|σK2|w2⟩ ->
    ECLOSED e2 /\ KCLOSED K2.
Proof.
  induction e1;
    intros;
    cbn in H1;
    try discriminate;
    invert_scoped H;
    try solve [inversion H1; subst; clear H1;
               intuition auto].
  - destruct K1; auto.
    inversion H1; subst.
    inversion H0; subst.
    intuition idtac.
    apply -> sub_preserves_scope_exp; eauto.
  - destruct K1; auto.
    inversion H1; subst.
    inversion H0; subst.
    intuition idtac.
    apply -> sub_preserves_scope_exp; eauto.
  - destruct e1_1; auto.
    inversion H1; subst; clear H1.
    intuition idtac.
    apply -> sub_preserves_scope_exp;
      eauto.
  - destruct e, e1; cbn; auto; unfold δ1 in H1; cbn;
      inversion H1; subst; clear H1;
        try destruct Req_EM_T;
        auto.
    inversion H2; subst; clear H2.
    intuition auto.
  - destruct e, e1_1, e1_2; cbn; unfold δ2 in H1; cbn;
      inversion H1; subst; clear H1;
        try (destruct Req_EM_T);
        try (destruct Rle_dec);
        try (destruct Rlt_dec);
        try (inversion H2; subst; clear H2);
          intuition auto.
  - destruct e1_1; cbn; cbn;
      inversion H1; subst; clear H1;
        try (destruct Rlt_dec);
        try (inversion H2; subst; clear H2);
          intuition auto.
  - destruct e1; auto.
    destruct Rle_dec; auto.
    inversion H1; subst; clear H1.
    eauto.
Qed.

Lemma step_weight_nonnegative : forall c1 w1 c2 w2,
    0 <= w1 ->
    step (mkConfiguration c1 w1) = Some (mkConfiguration c2 w2) ->
    0 <= w2.
Proof.
  intros c1 w1 c2 w2 Hw Hstep.
  destruct c1, c2;
    try solve [inversion Hstep].
  - solve_step e K Hstep.
    destruct K;
      inversion Hstep.
    destruct (Indicator_range A r0) as [Hindicator|Hindicator];
      rewrite Hindicator;
      cbn in *;
      auto.
  - solve_step e K Hstep.
    cbn in *.
    destruct Rle_dec;
      inversion Hstep;
      subst.
    apply Rmult_le_pos;
      auto.
Qed.

Lemma step_weight_linear : forall c r c' r' w,
    step ⟨c | r⟩ = Some ⟨ c' | r' ⟩ ->
    step ⟨c | w * r⟩ = Some ⟨ c' | w * r' ⟩.
Proof.
  intros.
  destruct c; auto.
  solve_step e K H.
  - destruct K; cbn in H;
      inversion H; subst;
        cbn;
        f_equal;
        f_equal;
        ring.
  - cbn in *.
    destruct Rle_dec; auto.
    inversion H; subst; clear H.
    f_equal.
    f_equal.
    ring.
Qed.

(* n or fewer steps *)
Fixpoint run (n : nat) (c : Configuration) : option Configuration :=
  match n with
  | 0%nat => Some c
  | S n' =>
    match c with
    | ⟨r⟩ => Some ⟨r⟩
    | _ => match step c with
           | None => None
           | Some c' => run n' c'
           end
    end
  end.

Ltac solve_run e K n H :=
  (* var *)
  let v := fresh "v" in
  (* const *)
  let r := fresh "r" in
  (* fun *)
  let b := fresh "b" in
  (* app *)
  let e1 := fresh "e1" in
  let e2 := fresh "e2" in
  (* seq *)
  let x := fresh "x" in
  let b := fresh "b" in
  (* op1 *)
  let o := fresh "o" in
  (* op2 *)
  let v1 := fresh "v1" in
  let v2 := fresh "v2" in
  (* cond *)
  let vp := fresh "vp" in
  let et := fresh "et" in
  let ef := fresh "ef" in
  (* factor *)
  let r := fresh "r" in
  destruct e as [v|r|b|e1 e2|x b|o v|o v1 v2|vp et ef| |r]; 
  [                             (* var *)
  |                             (* const *)
  |                             (* fun *)
  |                             (* app *)
  |                             (* seq *)
  |destruct o, v; auto             (* op1 *)
  |destruct o, v1, v2; auto            (* op2 *)
  |destruct vp; auto            (* cond *)
  |                             (* sample *)
  |destruct r; auto];           (* factor *)
  try solve
      [cbn in *;
       unfold δ1 in *;
       unfold δ2 in *;
       try destruct e1;
       try destruct Rle_dec;
       try destruct Rlt_dec;
       try destruct Req_EM_T;
       eauto;
       destruct K;
       destruct n;
       inversion H;
       cbn in *;
       eauto].


Lemma run_done : forall n r,
    run n ⟨r⟩ = Some ⟨r⟩.
Proof.
  destruct n;
    auto.
Qed.

Lemma run_step : forall n c1 c2,
    step c1 = Some c2 ->
    run (S n) c1 = run n c2.
Proof.
  intros n c1 c2 H.
  destruct c1 as [[|σ e K]];
    auto.
  solve_run e K n H.
Qed.

Open Scope nat.

Lemma run_transitive : forall n1 n2 c1 c2 c3,
    run n1 c1 = Some c2 ->
    run n2 c2 = c3 ->
    run (n1+n2) c1 = c3.
Proof.
  induction n1; intros.
  - inversion H;
      auto.
  - simpl (S n1 + n2).
    destruct c1 as [[|σ e K] w1].
    + rewrite run_done in H.
      inversion H; subst.
      cbn.
      destruct n2; auto.
    + solve_run e K (S (n1 + n2)) H.
Qed.

Theorem run_intermediate_exists : forall {n1 n2 c1 c3},
    run (n1+n2) c1 = Some c3 ->
    exists c2, run n1 c1 = Some c2 /\
               run n2 c2 = Some c3.
Proof.
  induction n1; intros.
  - cbn in *.
    eexists; intuition.
  - destruct c1.
    destruct c.
    + inversion H; subst.
      firstorder using run_done.
    + solve_step e K H;
        destruct K; cbn; auto.
Qed.

Theorem run_intermediate : forall n j,
    j <= n ->
    forall c1 c2 c3,
      run j c1 = Some c2 ->
      run n c1 = Some c3 ->
      run (n-j) c2 = Some c3.
Proof.
  intros.
  rewrite <- H1.
  replace n with (j+(n-j)) at 2 by auto.
  erewrite run_transitive with (n2:=n-j); eauto.
Qed.

Lemma run_preserves_environment : forall {n e1 σ1 K1 σK1 w1 σ2 e2 K2 σK2 w2},
    ECLOSED e1 ->
    KCLOSED K1 ->
    run n ⟨σ1|e1|K1|σK1|w1⟩ = Some ⟨σ2|e2|K2|σK2|w2⟩ ->
    ECLOSED e2 /\ KCLOSED K2.
Proof.
  induction n;
    intros.
  - cbn in H1.
    inversion H1; subst; auto.
  - replace (S n) with (1 + n) in H1 by auto.
    eapply run_intermediate_exists in H1.
    destruct H1 as [c2 [Hstep Hc2]].
    unfold run in Hstep.
    remember (step ⟨ σ1 | e1 | K1 | σK1 | w1 ⟩).
    destruct o; try discriminate.
    rewrite Heqo in Hstep.
    clear Heqo.
    destruct c2.
    destruct c0;
      try solve [destruct n; auto].
    apply step_preserves_environment in Hstep;
      auto.
    apply IHn in Hc2;
      intuition auto.
Qed.

Open Scope R.

Lemma run_weight_nonnegative : forall n c1 w1 c2 w2,
    0 <= w1 ->
    run n ⟨c1|w1⟩ = Some ⟨c2|w2⟩ ->
    0 <= w2.
Proof.
  induction n;
    intros c1 w1 c2 w2 Hc1 Hrun.
  - destruct c1;
      inversion Hrun;
      subst;
      simpl in *;
      auto.
  - replace (S n) with (1 + n)%nat in Hrun by auto.
    apply run_intermediate_exists in Hrun.
    destruct Hrun as [c3 [Hstep Hrun]].
    unfold run in Hstep.
    destruct c1.
    + inversion Hstep; subst.
      destruct n; cbn in Hrun;
        inversion Hrun; subst; auto.
    + remember (step ⟨ σ | e | K | σK | w1 ⟩).
      destruct o; try discriminate.
      rewrite Heqo in Hstep.
      clear Heqo.
      destruct c3.
      apply (step_weight_nonnegative _ _ _ _ Hc1) in Hstep.
      eapply IHn; eauto.
Qed.

Definition eval (n : nat) (c : Configuration) : R :=
  match run n c with
  | Some ⟨r⟩ => r
  | _ => 0
  end.

Lemma eval_done : forall n r, eval n ⟨r⟩ = r.
Proof.
  destruct n;
    auto.
Qed.

Hint Resolve eval_done.

(* Lemma 4.1 part 1 *)
Lemma eval_step : forall n c1 c2,
    step c1 = Some c2 ->
    eval (S n) c1 = eval n c2.
Proof.
  intros n c1 c2 Hstep.
  destruct c1 as [[|σ e K] w1];
    auto.
  unfold eval in *.
  solve_step e K Hstep.
Qed.

Lemma eval_weight_nonnegative : forall n c w,
    0 <= w ->
    0 <= eval n ⟨c|w⟩.
Proof.
  intros.
  unfold eval in *.
  remember (run n ⟨c|w⟩) as c' eqn:Hc'.
  destruct c' as [[[|? ? ?] ?]|]; auto.
  eapply run_weight_nonnegative;
    eauto.
Qed.

Definition eval_star (c : Configuration) : Rbar :=
  Lim_seq (fun n => eval n c).

Lemma eval_star_done : forall r,
    eval_star ⟨r⟩ = r.
Proof.
  intros.
  unfold eval_star.
  apply is_lim_seq_unique.
  apply is_LimSup_LimInf_lim_seq.
  - unfold is_LimSup_seq.
    intros.
    destruct eps; simpl.
    split.
    intros.
    exists N.
    split; auto.
    + destruct N;
        cbn;
        auto.
    + exists 0%nat.
      intros.
      destruct n;
        cbn;
        auto.
  - unfold is_LimInf_seq.
    intros.
    destruct eps; simpl.
    split.
    + intros.
      exists N.
      destruct N;
        split;
        cbn;
        auto.
    + exists 0%nat.
      intros.
      cbn.
      destruct n; cbn; auto.
Qed.

(* Lemma 4.1 part 2. *)
Lemma eval_star_step : forall c1 c2,
    step c1 = Some c2 ->
    eval_star c1 = eval_star c2.
Proof.
  intros.
  unfold eval_star in *.
  rewrite <- Lim_seq_incr_1.
  apply Lim_seq_ext.
  auto using eval_step.
Qed.

Lemma run_index_monotonic_None : forall n c,
    run n c = None ->
    run (S n) c = None.
Proof.
  induction n; intros.
  - inversion H.
  - destruct c as [[|? ? ?] ?].
    + rewrite run_done in H.
      inversion H.
    + destruct e;
        auto;
        try solve [destruct K;
                   try solve [inversion H];
                   erewrite run_step;
                   erewrite run_step in H;
                   try reflexivity;
                   eauto].
      * destruct K; auto.
        simpl in H.
        erewrite run_step; eauto.
      * destruct e1; auto.
        erewrite run_step by (cbn; eauto).
        erewrite run_step in H by (cbn; eauto).
        eauto.
      * destruct e, e0;
          cbn in *;
          try destruct Req_EM_T;
          auto;
          firstorder idtac.
      * destruct e1, e2, e3;
          cbn in *;
          try destruct Req_EM_T;
          try destruct Rle_dec;
          try destruct Rlt_dec;
          auto;
          firstorder idtac.
      * destruct e1, e2, e3;
          cbn in *;
          try destruct Rlt_dec;
          auto;
          firstorder idtac.
      * cbn in *.
        destruct e; cbn; auto.
        destruct Rle_dec; cbn; auto.
        destruct K; cbn; auto;
        firstorder idtac.
Qed.

Lemma run_index_monotonic_Some : forall n c r,
    run n c = Some ⟨r⟩ ->
    run (S n) c = Some ⟨r⟩.
Proof.
  intros.
  replace (S n) with (n + 1)%nat by auto.
  eapply run_transitive.
  apply H.
  auto.
Qed.

Lemma eval_index_monotonic_1 : forall n c w,
    0 <= w ->
    eval n ⟨c|w⟩ <= eval (S n) ⟨c|w⟩.
Proof.
  intros.
  unfold eval.
  remember (run n ⟨c|w⟩) as s eqn:Hrun_n;
    symmetry in Hrun_n.
  destruct s as [c'|].
  - destruct c' as [[|? ? ?] ?].
    + eapply run_index_monotonic_Some in Hrun_n.
      rewrite Hrun_n.
      auto using Rle_refl.
    + remember (run (S n) ⟨c|w⟩) as s eqn:Hrun_Sn;
        symmetry in Hrun_Sn.
      destruct s as [c'|]; auto using Rle_refl.
      destruct c' as [[|? ? ?] ?]; auto using Rle_refl.
      pose proof (run_weight_nonnegative (S n) c w Configuration_done w1 H).
      auto.
  - rewrite run_index_monotonic_None;
      auto using Rle_refl.
Qed.

Lemma eval_index_monotonic : forall n m (Hnm : (n <= m)%nat) c w,
    0 <= w ->
    eval n ⟨c|w⟩ <= eval m ⟨c|w⟩.
Proof.
  induction 1; intros;
    eauto using Rle_trans, eval_index_monotonic_1.
Qed.

Lemma eval_step_monotonic : forall n c w c' w',
    0 <= w ->
    step ⟨c|w⟩ = Some ⟨c'|w'⟩ ->
    eval n ⟨c|w⟩ <= eval n ⟨c'|w'⟩.
Proof.
  destruct n; intros.
  - pose proof (step_weight_nonnegative _ _ _ _ H H0).
    destruct c, c'; auto using Rle_refl.
  - erewrite eval_step by eauto.
    eauto using eval_index_monotonic, step_weight_nonnegative. 
Qed.

(* Lemma 4.2 part 1 *)
Lemma run_weight_linear : forall n σ e K σK r r',
    run n ⟨ σ | e | K | σK | r ⟩ = Some ⟨r'⟩ <->
    (forall w, w > 0 -> run n ⟨ σ | e | K | σK | w * r ⟩ = Some ⟨w * r'⟩).
Proof.
  induction n;
    split;
    intros;
    auto.
  intros.
  { specialize (H 1).
    replace (1 * r) with r in H by ring.
    replace (1 * r') with r' in H by ring.
    apply H.
    auto.
  }
  {
    assert (forall (σ : Entropy) (e : Expr) (K : Kont) (σK : Entropy) (r r' : R),
               run n ⟨ σ | e | K | σK | r ⟩ = Some ⟨ r' ⟩ ->
               (forall w : R, w > 0 -> run n ⟨ σ | e | K | σK | w * r ⟩ = Some ⟨ w * r' ⟩))
      by (apply IHn).
    solve_run e K n H.
    - destruct K;
        cbn in *;
        auto.
      destruct n;
        inversion H;
        subst;
        cbn in *;
        f_equal;
        f_equal;
        ring.
    - cbn in *.
      try destruct Rle_dec;
        auto.
      eapply IHn in H;
        eauto.
      replace (w * r * r0)
        with (w * (r * r0))
        by ring.
      eauto.
  }
  { assert 
      (forall (σ : Entropy) (e : Expr) (K : Kont) (σK : Entropy) (r r' : R),
          (forall w, w > 0 -> run n ⟨ σ | e | K | σK | w * r ⟩ = Some ⟨ w * r' ⟩) ->
          run n ⟨ σ | e | K | σK | r ⟩ = Some ⟨ r' ⟩)
      by (apply IHn).
    specialize (H 1).
    replace (1 * r) with r in H by ring.
    replace (1 * r') with r' in H by ring.
    apply H.
    auto.
  }
Qed.

(* Lemma 4.2 part 1 (as stated in paper) *)
Lemma run_weight_linear_alt : forall n σ e K σK w',
    run n ⟨ σ | e | K | σK | 1 ⟩ = Some ⟨w'⟩ <->
    (forall w, w > 0 -> run n ⟨ σ | e | K | σK | w ⟩ = Some ⟨w' * w⟩).
Proof.
  split; intros.
  - apply run_weight_linear with (w:=w) in H; auto.
    replace (w*1) with w in H by ring.
    replace (w*w') with (w'*w) in H by ring.
    auto.
  - apply run_weight_linear.
    intros.
    replace (w*1) with w by ring.
    replace (w*w') with (w'*w) by ring.
    apply H.
    auto.
Qed.

Lemma run_None : forall n σ e K σK r,
    run n ⟨ σ | e | K | σK | r ⟩ = None ->
    forall r', run n ⟨ σ | e | K | σK | r' ⟩ = None.
Proof.
  induction n;
    intros.
  - cbn in H.
    inversion H.
  - solve_run e K n H.
    + cbn in *.
      destruct K.
      * destruct n; inversion H.
      * eapply IHn. 
        eauto.
    + cbn in *.
      destruct K; auto.
      eapply IHn. 
      eauto.
Qed.

Lemma run_weight_0 : forall n c1 c2 w,
    run n ⟨c1|0⟩ = Some ⟨c2|w⟩ ->
    w = 0.
Proof.
  intros n c1 c2 w.
  revert c1.
  induction n; intros.
  - cbn in H.
    inversion H; subst.
    auto.
  - destruct c1.
    + rewrite run_done in H.
      inversion H; subst.
      auto.
    + solve_run e K n H.
      * destruct K;
          cbn in H.
        -- rewrite run_done in H.
           inversion H; subst.
           ring.
        -- eapply IHn.
           eapply H.
      * cbn in H.
        destruct K in H; auto.
        eapply IHn; eauto.
      * cbn in H.
        destruct Rle_dec; auto.
        replace (0 * r) with 0 in H by ring.
        eapply IHn.
        eauto.
Qed.

Lemma Rlt_0_not_eq_0 : forall {x}, 0 < x -> x <> 0.
Proof.
  intros.
  intro.
  subst.
  auto.
Qed.

Lemma run_Some_more : forall n c r c' r',
    r <> 0 ->
    run n ⟨ c | r ⟩ = Some ⟨ c' | r' ⟩ ->
    forall r2, run n ⟨ c | r2 ⟩ = Some ⟨ c' | (r2/r)*r'⟩.
Proof.
  induction n;
    intros;
    destruct c as [|? ? ?];
    try solve [inversion H0; subst;
               cbn;
               repeat f_equal;
               field; eauto].
  solve_run e K n H0.
  + destruct K; cbn in *; auto.
    rewrite run_done in H0.
    inversion H0; subst; clear H0.
    destruct n; cbn;
      f_equal;
      f_equal;
      field;
      auto.
  + destruct K; cbn in *; auto.
  + cbn in *.
    destruct (Rle_dec 0 r0); auto.
    destruct (Rlt_dec 0 r0).
    * assert (r0 <> 0).
      { intro; subst.
        auto.
      }
      replace (r2/r) with ((r2*r0)/(r*r0)) by (field; auto).
      eapply IHn.
      eapply Rmult_integral_contrapositive; intuition.
      eapply H0.
    * assert (r0 = 0) by (inversion r1; auto); subst.
      replace (r*0) with 0 in H0 by ring.
      replace (r2*0) with 0 by ring.
      pose proof (run_weight_0 _ _ _ _ H0); subst.
      replace (r2 / r * 0) with 0 by (field; auto).
      auto.
Qed.

Lemma run_Some_done : forall n σ e K σK r r',
    run n ⟨ σ | e | K | σK | r ⟩ = Some ⟨ r' ⟩ ->
    forall r2, exists r2', run n ⟨ σ | e | K | σK | r2 ⟩ = Some ⟨ r2' ⟩.
Proof.
  induction n;
    intros.
  - inversion H.
  - solve_run e K n H.
Qed.

Lemma step_Some_done : forall σ e K σK r r',
    step ⟨ σ | e | K | σK | r ⟩ = Some ⟨ r' ⟩ ->
    forall r2, exists r2', step ⟨ σ | e | K | σK | r2 ⟩ = Some ⟨ r2' ⟩.
Proof.
  intros.
  solve_step e K H.
Qed.

(* Lemma 4.2 part 2 *)
Lemma eval_weight_linear : forall n c w r,
    eval n ⟨c|w*r⟩ = w * eval n ⟨c|r⟩.
Proof.
  induction n; intros.
  - destruct c; cbn; ring.
  - remember (step ⟨ c | r ⟩) as s eqn:Hs.
    symmetry in Hs.
    destruct s as [[]|].
    + pose proof (step_weight_linear c r c0 w0 w Hs).
      rewrite eval_step with (c2:=⟨c0|w*w0⟩); auto.
      rewrite IHn.
      f_equal.
      symmetry.
      eapply eval_step; eauto.
    + unfold eval.
      destruct c.
      * cbn; ring.
      * assert (run (S n) ⟨ σ | e | K | σK | w * r ⟩ = None)
          by solve_run e K n Hs.
        rewrite H.
        assert (run (S n) ⟨ σ | e | K | σK | r ⟩ = None)
          by solve_run e K n Hs.
        rewrite H0.
        ring.
Qed.

(* Lemma 4.2 part 2 (as stated in paper) *)
Lemma eval_weight_linear_alt : forall n c w,
    eval n ⟨c|w⟩ = w * eval n ⟨c|1⟩.
Proof.
  intros.
  replace w with (w*1) at 1 by ring.
  apply eval_weight_linear.
Qed.

(* Lemma 4.2 part 2 *)
Lemma eval_star_weight_linear : forall σ e K σK w r,
    eval_star ⟨σ|e|K|σK|w*r⟩ = Rbar_mult w (eval_star ⟨σ|e|K|σK|r⟩).
Proof.
  intros.
  unfold eval_star.
  rewrite <- Lim_seq_scal_l.
  f_equal.
  extensionality n.
  apply eval_weight_linear.
Qed.

(* Lemma 4.2 part 2 (as stated in paper) *)
Lemma eval_star_weight_linear_alt : forall σ e K σK w,
    eval_star ⟨σ|e|K|σK|w⟩ = Rbar_mult w (eval_star ⟨σ|e|K|σK|1⟩).
Proof.
  intros.
  replace w with (w*1) at 1 by ring.
  apply eval_star_weight_linear.
Qed.

(*** eval step lemmas *)
Lemma eval_step_Seq : forall {n e1 e2 K σ1 σ2},
    eval (S n) ⟨ σ1 | Seq e1 e2 | K | σ2 | 1 ⟩ =
    eval n ⟨ Entropy_π1 σ1 | e1 | e2 -: K | (Entropy_π2 σ1)#σ2 | 1 ⟩.
Proof.
  auto using eval_step.
Qed.

Lemma eval_step_Return : forall {n v e K σ1 σ2},
    VCLOSED v ->
    eval (S n) ⟨ σ1 | v | e -: K | σ2 | 1 ⟩ =
    eval n ⟨ Entropy_π1 σ2 | e.[v/] | K | Entropy_π2 σ2 | 1 ⟩.
Proof.
  intros.
  eapply eval_step.
  cbn.
  inversion H; subst; auto.
Qed.

Lemma eval_step_App : forall {n v b K σ1 σ2},
    eval (S n) ⟨ σ1 | App (Fun b) v | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | b.[v/] | K | σ2 | 1 ⟩.
Proof.
  auto using eval_step.
Qed.

Lemma eval_step_Op1_Exp : forall {n r K σ1 σ2},
    eval (S n) ⟨ σ1 | Op1 Exp (Const r) | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | Const (Rexp r) | K | σ2 | 1 ⟩.
Proof.
  auto using eval_step.
Qed.

Lemma eval_step_Op1_Log : forall {n r K σ1 σ2},
    r <> 0 ->
    eval (S n) ⟨ σ1 | Op1 Log (Const r) | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | Const (Rlog r) | K | σ2 | 1 ⟩.
Proof.
  intros.
  eapply eval_step.
  cbn.
  destruct Req_EM_T; auto.
  exfalso; auto.
Qed.

Lemma eval_step_Op1_Realp_1 : forall {n r K σ1 σ2},
    eval (S n) ⟨ σ1 | Op1 Realp (Const r) | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | Const 1%R | K | σ2 | 1 ⟩.
Proof.
  eauto using eval_step.
Qed.

Lemma eval_step_Op1_Realp_0 : forall {n b K σ1 σ2},
    eval (S n) ⟨ σ1 | Op1 Realp (Fun b) | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | Const 0%R | K | σ2 | 1 ⟩.
Proof.
  eauto using eval_step.
Qed.

Lemma eval_step_Op2_Plus : forall {n r1 r2 K σ1 σ2},
    eval (S n) ⟨ σ1 | Op2 Plus (Const r1) (Const r2) | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | Const (Rplus r1 r2) | K | σ2 | 1 ⟩.
Proof.
  auto using eval_step.
Qed.

Lemma eval_step_Op2_Minus : forall {n r1 r2 K σ1 σ2},
    eval (S n) ⟨ σ1 | Op2 Minus (Const r1) (Const r2) | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | Const (Rminus r1 r2) | K | σ2 | 1 ⟩.
Proof.
  auto using eval_step.
Qed.

Lemma eval_step_Op2_Times : forall {n r1 r2 K σ1 σ2},
    eval (S n) ⟨ σ1 | Op2 Times (Const r1) (Const r2) | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | Const (Rmult r1 r2) | K | σ2 | 1 ⟩.
Proof.
  auto using eval_step.
Qed.

Lemma eval_step_Op2_Div : forall {n r1 r2 K σ1 σ2},
    r2 <> 0 ->
    eval (S n) ⟨ σ1 | Op2 Div (Const r1) (Const r2) | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | Const (Rdiv r1 r2) | K | σ2 | 1 ⟩.
Proof.
  intros.
  eapply eval_step.
  cbn.
  destruct Req_EM_T; auto.
  exfalso; auto.
Qed.

Lemma eval_step_Op2_Le_1 : forall {n r1 r2 K σ1 σ2},
    r1 <= r2 ->
    eval (S n) ⟨ σ1 | Op2 Le (Const r1) (Const r2) | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | Const 1%R | K | σ2 | 1 ⟩.
Proof.
  intros.
  eapply eval_step.
  cbn.
  destruct Rle_dec; auto.
Qed.

Lemma eval_step_Op2_Le_0 : forall {n r1 r2 K σ1 σ2},
    r2 < r1 ->
    eval (S n) ⟨ σ1 | Op2 Le (Const r1) (Const r2) | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | Const 0%R | K | σ2 | 1 ⟩.
Proof.
  intros.
  eapply eval_step.
  cbn.
  destruct Rle_dec; auto.
  exfalso; auto.
Qed.

Lemma eval_step_Op2_Lt_1 : forall {n r1 r2 K σ1 σ2},
    r1 < r2 ->
    eval (S n) ⟨ σ1 | Op2 Lt (Const r1) (Const r2) | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | Const 1%R | K | σ2 | 1 ⟩.
Proof.
  intros.
  eapply eval_step.
  cbn.
  destruct Rlt_dec; auto.
Qed.

Lemma eval_step_Op2_Lt_0 : forall {n r1 r2 K σ1 σ2},
    r2 <= r1 ->
    eval (S n) ⟨ σ1 | Op2 Lt (Const r1) (Const r2) | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | Const 0%R | K | σ2 | 1 ⟩.
Proof.
  intros.
  eapply eval_step.
  cbn.
  destruct Rlt_dec; auto.
  exfalso; auto.
Qed.

Lemma eval_step_Cond_true : forall {n r et ef K σ1 σ2},
    0 < r ->
    eval (S n) ⟨ σ1 | Cond (Const r) et ef | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | et | K | σ2 | 1 ⟩.
Proof.
  intros.
  eapply eval_step.
  cbn.
  destruct Rlt_dec; auto.
Qed.

Lemma eval_step_Cond_false : forall {n r et ef K σ1 σ2},
    r <= 0 ->
    eval (S n) ⟨ σ1 | Cond (Const r) et ef | K | σ2 | 1 ⟩ =
    eval n ⟨ σ1 | ef | K | σ2 | 1 ⟩.
Proof.
  intros.
  eapply eval_step.
  cbn.
  destruct Rlt_dec; auto.
  exfalso; auto.
Qed.

Lemma eval_step_Sample : forall {n K σ1 σ2},
    eval (S n) ⟨ σ1 | Sample | K | σ2 | 1 ⟩ =
    eval n ⟨ Entropy_π1 σ1 | (Const (Entropy_extract (Entropy_π2 σ1))) | K | σ2 | 1 ⟩.
Proof.
  auto using eval_step.
Qed.

Lemma eval_step_Factor : forall {n r K σ1 σ2},
    0 <= r ->
    eval (S n) ⟨ σ1 | Factor (Const r) | K | σ2 | 1 ⟩ =
    r * (eval n ⟨ σ1 | Const r | K | σ2 | 1 ⟩).
Proof.
  intros.
  rewrite <- eval_weight_linear.
  apply eval_step.
  cbn.
  destruct Rle_dec.
  - replace (1*r) with (r*1) by ring.
    trivial.
  - apply n0 in H.
    auto.
Qed.
