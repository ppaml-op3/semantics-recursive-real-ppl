Require Import Coq.Program.Program.
Require Import Coq.Program.Tactics.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Reals.Reals.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Lim_seq.
Require Import Autosubst.Autosubst.
Require Import Coq.Logic.Decidable.

Require Import Biorthogonality.Basics.
Require Import Biorthogonality.Measures.
Require Import Biorthogonality.Syntax.
Require Import Biorthogonality.OpSem.
Require Import Biorthogonality.MeasSem.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope nat.

Local Obligation Tactic := idtac.
Program Fixpoint find_smallest_helper
        {P : nat -> Prop}
        (P_dec : forall n, decidable (P n))
        (cur : nat)
        (n : nat)
        (Hcur : (forall i, i < cur -> ~ P i) -> (forall i, i < n -> ~ P i))
        (Hn : P n) :
  exists n, P n /\ forall i, i < n -> ~ P i :=
  match cur with
  | 0 =>
    match P_dec 0 with
    | or_introl yes => ex_intro _ 0 _
    | or_intror no => ex_intro _ n _
    end
  | S cur' =>
    match P_dec cur' with
    | or_introl yes => find_smallest_helper P_dec cur' cur' id yes
    | or_intror no => find_smallest_helper P_dec cur' n _ Hn
    end
  end.
Obligation 1. program_simpl. Qed.
Obligation 2. program_simpl. Qed.
Obligation 3.
intros.
subst.
apply Hcur; auto.
intros.
inversion H1; subst; auto.
Qed.

Definition find_smallest
           {P : nat -> Prop}
           (P_dec : forall n, decidable (P n))
           (n : nat)
           (Hn : P n) :
  exists n, P n /\ forall i, i < n -> ~ P i :=
  find_smallest_helper P_dec n n id Hn.

Definition ex_least (P : nat -> Prop) :=
  exists j, P j /\ (forall j', P j' -> j <= j').

Notation "'exists_least' j , P" := (ex_least (fun j => P)) (at level 200).

Lemma smallest_alt : forall {P : nat -> Prop},
    (exists n, P n /\ forall i, i < n -> ~ P i) ->
    exists_least n, P n.
Proof.
  intros.
  destruct H as [n Hn].
  exists n.
  intuition auto.
  destruct (lt_dec j' n); auto.
  exfalso.
  apply H0 in H1; auto.
Qed.

Definition find_smallest_alt
           {P : nat -> Prop}
           (P_dec : forall n, decidable (P n))
           (H : exists n, P n) :
  exists_least n, P n :=
  let (n,Hn) := H in smallest_alt (find_smallest P_dec n Hn).
Opaque find_smallest_alt.

(* Definition 4.3 *)
Inductive K_gt : Kont -> Entropy -> Kont -> Entropy -> Prop :=
| K_nil : forall K σ, K_gt K σ K σ
| K_cons : forall K1 σ1 K2 σ2 e σ,
    K_gt K2 σ2 K1 σ1 ->
    K_gt (e-:K2) (σ#σ2) K1 σ1.

Local Hint Constructors K_gt.

Definition ConfigClosed c :=
  match c with
  | mkConfiguration (Configuration_more _ e K _) _ => ECLOSED e /\ KCLOSED K
  | mkConfiguration (Configuration_done _) _ => True
  end.

Lemma step_closed : forall c,
    ConfigClosed c ->
    match step c with
    | None => True
    | Some c' => ConfigClosed c'
    end.
Proof.
  intros.
  unfold ConfigClosed in H.
  destruct c.
  destruct c; try solve [cbn; auto].
  solve_step e K H.
  - cbn.
    destruct K; cbn; intuition auto.
    + inversion H1; subst.
      apply -> sub_preserves_scope_exp; eauto.
    + inversion H1; subst.
      auto.
  - destruct K; cbn; intuition auto.
    + inversion H1; subst.
      apply -> sub_preserves_scope_exp; eauto.
    + inversion H1; subst.
      auto.
  - cbn.
    destruct e1; cbn; intuition auto.
    inversion H1; subst.
    + apply -> sub_preserves_scope_exp; eauto.
    + apply -> sub_preserves_scope_exp; eauto.
Qed.

Lemma run_closed : forall n c,
    ConfigClosed c ->
    match run n c with
    | None => True
    | Some c' => ConfigClosed c'
    end.
Proof.
  induction n; intros; auto.
  destruct c.
  destruct c; auto.
  destruct e;
    try solve_inversion;
    auto;
    try solve
        [cbn;
         destruct K;
         try destruct e1;
         try (destruct e; auto;
              destruct Rlt_dec; auto);
         try
         auto;
         apply IHn;
         cbn;
         auto;
         inversion H;
         inversion H1; subst;
         try (inversion H0; subst);
         intuition auto;
         try solve_inversion;
         apply -> sub_preserves_scope_exp;
         eauto].
  - unfold δ1;
      destruct e;
      destruct e0;
      cbn;
      try destruct Req_EM_T;
      cbn;
      auto;
      apply IHn;
      inversion H; subst;
      repeat (constructor; auto).
  - unfold δ2;
      destruct e1, e2, e3;
      cbn;
      try destruct Req_EM_T;
      try destruct Rle_dec;
      try destruct Rlt_dec;
      auto;
      apply IHn;
      inversion H; subst;
      repeat (constructor; auto).
  - inversion H; subst.
    inversion H0; subst;
      destruct e1;
      cbn;
      try destruct Rlt_dec;
      auto;
      apply IHn;
      repeat (constructor; eauto).
Qed.

Fixpoint Kont_end (K : Kont) (σ : Entropy) : Entropy :=
  match K with
  | Knil => σ
  | Kcons e K' => Kont_end K' (Entropy_π2 σ)
  end.

Lemma run_Kont_determined : forall {n σ1 e1 K1 σ1' w1
                                      σ2 e2 K2 σ2' w2},
    run n ⟨ σ1 | e1 | K1 | σ1' | w1 ⟩ = Some ⟨ σ2 | e2 | K2 | σ2' | w2 ⟩ ->
    Kont_end K1 σ1' = Kont_end K2 σ2'.
Proof.
  induction n; intros.
  - cbn in H.
    inversion H; subst; intuition.
  - solve_run e1 K1 n H.
    apply IHn in H.
    cbn in H.
    rewrite interpolate_project_2 in H.
    auto.
Qed.

Lemma run_Knil_determined : forall {n σ1 e1 σ1' w1
                                      σ2 e2 σ2' w2},
    run n ⟨ σ1 | e1 | Knil | σ1' | w1 ⟩ = Some ⟨ σ2 | e2 | Knil | σ2' | w2 ⟩ ->
    σ1' = σ2'.
Proof.
  intros.
  apply run_Kont_determined in H.
  inversion H; subst; auto.
Qed.

Definition ConfigKont_picked (c : Configuration) j :=
  match c, run j c with
  | mkConfiguration (Configuration_more _ _ K0 σK0) _,
    Some (mkConfiguration (Configuration_more _ ej Kj σKj) _) =>
    VCLOSED ej /\ Kj = K0 /\ σKj = σK0
  | _, _ => False
  end.

Lemma ConfigKont_picked_dec (c : Configuration) : forall j,
    decidable (ConfigKont_picked c j).
Proof.
  intros.
  unfold decidable.
  unfold ConfigKont_picked.
  destruct c.
  destruct c; auto.
  remember (run j ⟨ σ | e | K | σK | w ⟩) as c.
  destruct c; auto.
  destruct c; auto.
  destruct c; auto.
  destruct (ValScoped_dec e0 0); [|right; intuition auto].
  destruct (Kont_eq_dec K0 K); [|right; intuition auto].
  destruct (Entropy_eq_dec σK0 σK); [|right; intuition auto].
  subst.
  left; intuition.
Qed.

Lemma run_fixpoint : forall n c v w,
    run n c = Some ⟨ v@w ⟩ ->
    run (S n) c = Some ⟨ v@w ⟩.
Proof.
  intros.
  replace (S n) with (n + 1) by auto.
  eapply run_transitive.
  apply H.
  cbn.
  auto.
Qed.

(* Lemma 4.4 {lemma-continuations-are-continuous} *)
Lemma continuations_are_continuous : forall i c,
    ConfigClosed c ->
    match c, run i c with
    | mkConfiguration (Configuration_more σ0 e0 K0 σK0) w0,
      Some (mkConfiguration (Configuration_more σi ei Ki σKi) wi) =>
      (exists_least j, j <= i /\ ConfigKont_picked c j) \/
      K_gt Ki σKi K0 σK0
    | _,_ => True
    end.
Proof.
  (** By induction on i. *)
  induction i;
    intros c0 Hclosed;
    destruct c0 as [[|σ0 e0 K0 σK0] w0];
    try solve [cbn; auto].
  remember (run (S i) ⟨ σ0 | e0 | K0 | σK0 | w0 ⟩) as cSi eqn:HcSi;
    destruct cSi as [[[|σSi eSi KSi σKSi] wSi]|];
    auto.
  (** Assume the proposition holds at i (IHi) and check at i+1. *)
  (* take apart (ci i) *)
  remember (run i ⟨ σ0 | e0 | K0 | σK0 | w0 ⟩) as ci eqn:Hci.
  destruct ci as [[[|σi ei Ki σKi] wi]|].
  { (* can't be final, there is a following step *)
    exfalso.
    symmetry in Hci.
    apply run_fixpoint in Hci.
    rewrite Hci in HcSi.
    inversion HcSi.
  }
  {
    specialize (IHi ⟨ σ0 | e0 | K0 | σK0 | w0 ⟩).
    specialize (IHi Hclosed).
    cbn in IHi.
    rewrite <- Hci in IHi.
    destruct IHi.
    { (** If property (a) holds for some j <= i, then (a) holds at i+1. *)
      left.
      destruct H as [j Hj].
      exists j.
      intuition auto.
      (* This is more complicated than the paper makes it seem. *)
      inversion H3; auto.
    }
    (* Assume property (b) holds at i. *)
    apply (run_closed i) in Hclosed.
    rewrite <- Hci in Hclosed.
    inversion Hclosed.
    inversion H0;
      subst;
      try solve                 (* not a value *)
          [right;
           replace (S i) with (i + 1) in HcSi by auto;
           erewrite run_transitive in HcSi; revgoals; eauto;
           cbn in HcSi;
           try (inversion H2; subst; auto);
           try (destruct Rlt_dec; auto);
           inversion HcSi; subst;
           inversion H; subst; auto].
    - right.                    (* Op1: not a value *)
      replace (S i) with (i + 1) in HcSi by auto.
      erewrite run_transitive in HcSi; eauto.
      destruct o, v; auto; cbn in HcSi;
        try destruct Req_EM_T; cbn in HcSi; auto;
          inversion HcSi; subst; auto.
    - right.                    (* Op2: not a value *)
      replace (S i) with (i + 1) in HcSi by auto.
      erewrite run_transitive in HcSi; eauto.
      destruct o, v1, v2; auto; cbn in HcSi;
        try destruct Req_EM_T;
        try destruct Rle_dec;
        try destruct Rlt_dec;
        cbn in HcSi; auto;
          inversion HcSi; subst; auto.
    - 
      (* is a value *)
      inversion H; subst; auto.
      + (* rule 1 *)
        left.
        assert (exists j : nat, (j <= S i /\ ConfigKont_picked ⟨ σ0 | e0 | K0 | σK0 | w0 ⟩ j)).
        { exists i.
          intuition auto.
          unfold ConfigKont_picked.
          rewrite <- Hci.
          intuition idtac.
        }
        apply find_smallest_alt; auto.
        intros.
        unfold decidable.
        destruct (ConfigKont_picked_dec ⟨ σ0 | e0 | K0 | σK0 | w0 ⟩ n);
          destruct (le_dec n (S i));
          intuition auto.
      + (* rule 2 *)
        right.
        replace (S i) with (i + 1) in HcSi by auto.
        symmetry in HcSi.
        eapply run_intermediate_exists in HcSi.
        destruct HcSi.
        destruct H4.
        rewrite H4 in Hci.
        inversion Hci; subst.
        clear Hci.
        destruct ei;
          try solve_inversion.
        * cbn in H5.
          inversion H5; subst.
          clear H5.
          rewrite interpolate_project_2.
          auto.
        * cbn in H5.
          inversion H5; subst.
          clear H5.
          rewrite interpolate_project_2.
          auto.
  } 
  { exfalso.
    replace (S i) with (i + 1) in HcSi by auto.
    symmetry in HcSi.
    eapply run_intermediate_exists in HcSi.
    destruct HcSi.
    destruct H.
    rewrite H in Hci.
    solve_inversion.
  }
Qed.

(* Theorem 4.5 {thm-interpolation} *)
Theorem interpolation : forall σ1 e1 K1 σ1' w1
                               σ3 e3 σ3' w3 n,
    ECLOSED e1 ->
    KCLOSED K1 ->
    VCLOSED e3 ->
    run n ⟨σ1|e1|K1|σ1'|w1⟩ = Some ⟨σ3|e3|Knil|σ3'|w3⟩ ->
    exists_least j, exists σ2 v w2,
      VCLOSED v /\
      run j ⟨σ1|e1|K1|σ1'|w1⟩ = Some ⟨σ2|v|K1|σ1'|w2⟩ /\
      run (n-j) ⟨σ2|v|K1|σ1'|w2⟩ = Some ⟨σ3|e3|Knil|σ3'|w3⟩.
Proof.
  intros.
  apply find_smallest_alt; revgoals.
  { destruct K1.
    - exists n.
      replace (n - n) with 0 by auto.
      destruct (run_Knil_determined H2); subst.
      repeat eexists; eauto.
    - assert
        (forall z j : nat,
            match run z ⟨ σ1 | e1 | e -: K1 | σ1' | w1 ⟩ with
            | Some cz => run j cz = run (j + z) ⟨ σ1 | e1 | e -: K1 | σ1' | w1 ⟩
            | None => None = run (j + z) ⟨ σ1 | e1 | e -: K1 | σ1' | w1 ⟩
            end).
      { intros.
        remember (run z ⟨ σ1 | e1 | e -: K1 | σ1' | w1 ⟩) as runz.
        destruct runz.
        - replace (j + z) with (z + j) by ring.
          erewrite run_transitive; eauto.
        - induction j; auto.
          simpl (S j + z).
          symmetry.
          apply run_index_monotonic_None.
          auto.
      }
      assert (ConfigClosed ⟨ σ1 | e1 | e -: K1 | σ1' | w1 ⟩)
        by (constructor; auto).
      pose proof (continuations_are_continuous n ⟨ σ1 | e1 | e -: K1 | σ1' | w1 ⟩ H4)
        as Hcont.
      cbn in Hcont.
      remember (run n ⟨ σ1 | e1 | e -: K1 | σ1' | w1 ⟩) as run_n.
      destruct run_n; try solve_inversion.
      destruct c.
      destruct c; try solve_inversion.
      inversion H2; subst; clear H2.
      inversion Hcont; subst; try solve_inversion.
      destruct H2.
      remember (run x ⟨ σ1 | e1 | e -: K1 | σ1' | w1 ⟩) as run_x.
      destruct run_x; intuition auto; try solve_inversion.
      destruct c; intuition auto.
      destruct c; intuition auto.
      subst.
      exists x.
      exists σ.
      exists e0.
      exists w.
      split; [|split]; auto.
      eapply run_intermediate; eauto.
  }
  intros.
  remember (run n0 ⟨ σ1 | e1 | K1 | σ1' | w1 ⟩) as c.
  destruct c; revgoals.
  { right.
    intro.
    destruct H3 as [? [? [? [? [? ?]]]]].
    inversion H4.
  }
  destruct c.
  destruct c.
  { right.
    intro.
    destruct H3 as [? [? [? [? [? ?]]]]].
    inversion H4.
  }
  destruct (ValScoped_dec e 0); revgoals.
  { right.
    intro.
    destruct H4 as [? [? [? [? [? ?]]]]].
    inversion H5; subst.
    auto.
  }
  assert (decidable (run (n - n0) ⟨ σ | e | K1 | σ1' | w ⟩ =
                     Some ⟨ σ3 | e3 | Knil | σ3' | w3 ⟩)).
  { remember (run (n - n0) ⟨ σ | e | K1 | σ1' | w ⟩) as c.
    destruct c; [|right; intro; solve_inversion].
    destruct c.
    destruct c; [right; intro; solve_inversion|].
    destruct (Entropy_eq_dec σ0 σ3);
      [|right; intro Hfalse; inversion Hfalse];
      subst;
      auto.
    destruct (Expr_eq_dec e0 e3);
      [|right; intro Hfalse; inversion Hfalse];
      subst;
      auto.
    destruct (Kont_eq_dec K0 Knil);
      [|right; intro Hfalse; inversion Hfalse];
      subst;
      auto.
    destruct (Entropy_eq_dec σK0 σ3');
      [|right; intro Hfalse; inversion Hfalse];
      subst;
      auto.
    destruct (Req_dec w0 w3);
      [|right; intro Hfalse; inversion Hfalse];
      subst;
      auto.
    left.
    auto.
  }
  inversion H4; revgoals.
  { right.
    intro.
    destruct H6 as [? [? [? [? [? ?]]]]].
    inversion H7; subst.
    auto.
  }
  destruct (Kont_eq_dec K K1); revgoals.
  { right.
    intro.
    destruct H7 as [? [? [? [? [? ?]]]]].
    inversion H8.
    auto.
  }
  subst.
  destruct (Entropy_eq_dec σK σ1'); revgoals.
  { right.
    intro.
    destruct H7 as [? [? [? [? [? ?]]]]].
    inversion H8.
    auto.
  }
  subst.
  left.
  exists σ.
  exists e.
  exists w.
  intuition auto.
Qed.

Inductive B (K1 K2 : Kont) (τ1 τ2 : Entropy) :
  Kont -> Entropy -> Kont -> Entropy -> Prop :=
| B_nil : B K1 K2 τ1 τ2 K1 τ1 K2 τ2
| B_cons : forall K K' τ τ' e σ,
    B K1 K2 τ1 τ2 K τ K' τ' ->
    B K1 K2 τ1 τ2 (e-:K) (σ#τ) (e-:K') (σ#τ').

Inductive RR (K1 K2 : Kont) (τ1 τ2 : Entropy) (r: R) :
  option Configuration -> option Configuration -> Prop :=
| RR_intro : forall σ e w K K' τ τ',
    B K1 K2 τ1 τ2 K τ K' τ' ->
    RR K1 K2 τ1 τ2 r (Some ⟨σ|e|K|τ|w⟩) (Some ⟨σ|e|K'|τ'|w * r⟩).

Fixpoint Kont_length (K : Kont) : nat :=
  match K with
  | Knil => 0
  | Kcons e K' => S (Kont_length K')
  end.

Lemma Kont_occurs : forall (x : Expr) (xs : Kont),
    x-:xs <> xs.
Proof.
  intros.
  intro.
  induction xs.
  - inversion H.
  - contradict IHxs.
    inversion H; subst.
    rewrite H2.
    rewrite H2.
    auto.
Qed.

Lemma B_length : forall K1 τ1 K2 τ2
                        K τ K' τ',
    B K1 K2 τ1 τ2 K τ K' τ' ->
    Kont_length K1 <= Kont_length K.
Proof.
  intros.
  dependent induction H; subst.
  - auto.
  - cbn.
    rewrite IHB; eauto.
Qed.

Lemma B_no_smaller : forall eK1 K1 τ1
                            K2 τ2 τ
                            K' τ',
    ~ (B (eK1 -: K1) K2 τ1 τ2 K1 τ K' τ').
Proof.
  intros.
  intro.
  apply B_length in H.
  cbn in H.
  auto.
Qed.

Theorem genericity : forall n σ σ' e v w' K1 K2 τ1 τ2 w1 w2,
    (w1 <> 0)%R ->
    ECLOSED e ->
    KCLOSED K1 ->
    KCLOSED K2 ->
    VCLOSED v ->
    run n ⟨σ|e|K1|τ1|w1⟩ = Some ⟨σ'|v|K1|τ1|w'*w1⟩ ->
    (forall i σ' v w',
        VCLOSED v ->
        run i ⟨σ|e|K1|τ1|w1⟩ = Some ⟨σ'|v|K1|τ1|w'*w1⟩ ->
        n <= i) ->
    run n ⟨σ|e|K2|τ2|w2⟩ = Some ⟨σ'|v|K2|τ2|w'*w2⟩.
Proof.
  intros.
  enough (forall i (Hi : i <= n),
             RR K1 K2 τ1 τ2 (w2/w1)
                (run i ⟨ σ | e | K1 | τ1 | w1 ⟩)
                (run i ⟨ σ | e | K2 | τ2 | w2 ⟩)).
  { specialize (H6 n (le_refl _)).
    rewrite H4 in H6.
    inversion H6; subst.
    inversion H8; subst.
    - field_simplify (w' * w1 * (w2 / w1))%R; auto.
      replace (w' * w2 / 1)%R with (w' * w2)%R by (field; auto).
      auto.
    - apply B_no_smaller in H7.
      auto.
  }
  intro i.
  (* revert w1 w2 τ1 τ2 K1 K2 w' e v σ σ' n H5 H4 H3 H2 H1 H0 H. *)
  induction i;
    intros.
  - cbn.
    replace w2 with (w1 * (w2/w1))%R at 2 by (field; auto).
    constructor.
    constructor.
  - specialize (IHi ltac:(auto)).
    replace n with (S i + (n - S i)) in H4 by auto.
    destruct (run_intermediate_exists H4) as [c2 [HSi_c2 _]].

    replace (S i) with (i + 1) in HSi_c2 by auto.
    destruct (run_intermediate_exists HSi_c2) as [c2' [Hi_c2 HSi_c2']].

    replace (i + 1) with (S i) in HSi_c2 by auto.
    rewrite <- HSi_c2' in HSi_c2.
    rewrite HSi_c2.
    inversion IHi.
    inversion H8; subst.
    + symmetry in H6.
      symmetry in H7.
      rewrite H6 in Hi_c2.
      pose proof H7.
      inversion Hi_c2; subst.
      eapply run_transitive with (n2:=1) in H7;
        try solve [reflexivity].
      replace (i + 1) with (S i) in H7 by auto.
      rewrite H7.
      destruct e0; auto;
        try solve_inversion;
        try solve [cbn; repeat constructor].
      * exfalso.
        replace w with ((w/w1) * w1)%R in H6 by (field; auto).
        specialize (H5 _ _ _ _ ltac:(auto) H6).
        auto.
      * exfalso.
        pose proof H6 as Henv.
        eapply run_preserves_environment in Henv; eauto.
        replace w with ((w/w1) * w1)%R in H6 by (field; auto).
        eapply H5 in H6; intuition auto.
      * destruct e0_1; auto; try solve_inversion.
        cbn.
        constructor.
        constructor.
      * destruct e0, e1; auto;
          cbn;
          cbn in HSi_c2';
          try destruct Req_EM_T;
          subst;
          try solve_inversion;
          auto;
          constructor;
          constructor.
      * destruct e0, e0_1, e0_2; auto;
          cbn;
          cbn in HSi_c2';
          try destruct Req_EM_T;
          try destruct Rle_dec;
          try destruct Rlt_dec;
          subst;
          try solve_inversion;
          auto;
          constructor;
          constructor.
      * destruct e0_1; auto;
          cbn;
          cbn in HSi_c2';
          try destruct Rlt_dec;
          subst;
          try solve_inversion;
          auto;
          constructor;
          constructor.
      * cbn.
        cbn in HSi_c2'.
        destruct e0; try solve_inversion.
        destruct Rlt_dec; try solve_inversion.
        replace (w * (w2 / w1) * r)%R with (w * r * (w2 / w1))%R by ring.
        constructor.
        constructor.
    + symmetry in H6.
      symmetry in H7.
      rewrite H6 in IHi.
      rewrite H7 in IHi.
      pose proof Hi_c2.
      rewrite H6 in Hi_c2.
      inversion Hi_c2; subst.
      clear Hi_c2.
      eapply run_transitive with (n2:=1) in H7;
        try solve [reflexivity].
      replace (i + 1) with (S i) in H7 by auto.
      rewrite H7.
      destruct e0;
        try solve_inversion;
        try solve [cbn; econstructor; eauto].
      * cbn.
        repeat rewrite interpolate_project_2.
        repeat rewrite interpolate_project_1.
        constructor.
        inversion H9; subst; auto.
      * cbn.
        repeat rewrite interpolate_project_2.
        repeat rewrite interpolate_project_1.
        constructor.
        inversion H9; subst; auto.
      * cbn.
        destruct e0_1; try solve_inversion.
        constructor.
        constructor.
        auto.
      * cbn.
        constructor.
        constructor.
        constructor.
        auto.
      * destruct e0, e2;
          cbn;
          cbn in HSi_c2';
          try destruct Req_EM_T;
          subst;
          try solve_inversion;
          auto;
          constructor;
          constructor;
          auto.
      * destruct e0, e0_1, e0_2;
          try solve [cbn in HSi_c2'; inversion HSi_c2'];
          cbn;
          cbn in HSi_c2';
          try destruct Req_EM_T;
          try destruct Rle_dec;
          try destruct Rlt_dec;
          subst;
          try solve_inversion;
          auto;
          constructor;
          constructor;
          auto.
      * destruct e0_1;
          cbn;
          cbn in HSi_c2';
          try destruct Rlt_dec;
          subst;
          try solve_inversion;
          auto;
          constructor;
          constructor;
          auto.
      * cbn in *.
        destruct e0; try solve_inversion.
        destruct Rlt_dec; try solve_inversion.
        replace (w * (w2 / w1) * r)%R with (w * r * (w2 / w1))%R by ring.
        constructor.
        constructor.
        auto.
Qed.
