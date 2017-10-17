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

Require Import Biorthogonality.Measures.
Require Import Biorthogonality.Basics.

Set Bullet Behavior "Strict Subproofs".

Local Hint Extern 9 =>
match goal with
| [ H : _ |- _ ] => solve [inversion H]
end.

Local Hint Extern 9 => contradiction.

Open Scope nat.

(*** Syntax. *)
Inductive EOp1 :=
| Log
| Exp
| Realp.

Lemma EOp1_eq_dec : forall (o1 o2 : EOp1),
    {o1 = o2} + {~ o1 = o2 }.
Proof.
  decide equality.
Qed.

Inductive EOp2 :=
| Plus
| Minus
| Times
| Div
| Lt
| Le.

Lemma EOp2_eq_dec : forall (o1 o2 : EOp2),
    {o1 = o2} + {~ o1 = o2 }.
Proof.
  decide equality.
Qed.

Inductive Expr : Type :=
| Var : var -> Expr
| Const : R -> Expr
| Fun : forall (b : {bind Expr}), Expr
| App : Expr -> Expr -> Expr
| Seq : Expr -> forall (b : {bind Expr}), Expr
| Op1 : EOp1 -> Expr -> Expr
| Op2 : EOp2 -> Expr -> Expr -> Expr
| Cond : Expr -> Expr -> Expr -> Expr
| Sample : Expr
| Factor : Expr -> Expr.

Arguments Const r.
Arguments Var v.
Arguments Fun b : assert.
Arguments App f v.
Arguments Seq e b.
Arguments Op1 v.
Arguments Op2 v1 v2.
Arguments Cond vp et ef.
Arguments Sample : assert.
Arguments Factor v : assert.

Lemma Expr_eq_dec : forall (e1 e2 : Expr),
    {e1 = e2} + {~ e1 = e2 }.
Proof.
  intros.
  decide equality.
  - apply Nat.eq_dec.
  - apply Req_EM_T.
  - apply EOp1_eq_dec.
  - apply EOp2_eq_dec.
Qed.

Instance IdSubst_Expr : Ids Expr. derive. Defined.
Instance Rename_Expr : Rename Expr. derive_Rename. Defined.
Instance Subst_Expr : Subst Expr. derive. Defined.
Instance SubstLemmas_Expr: SubstLemmas Expr. derive. Defined.

Reserved Notation "'EXP' Γ ⊢ e"
         (at level 69, no associativity).

Reserved Notation "'VAL' Γ ⊢ v"
         (at level 69, no associativity).

Definition Env := nat.

Inductive ExpScoped (Γ : Env) : forall (e : Expr), Prop :=
| ExpScoped_App : forall f v,
    VAL Γ ⊢ f ->
    VAL Γ ⊢ v ->
    EXP Γ ⊢ App f v
| ExpScoped_Seq : forall e b,
    EXP Γ ⊢ e ->
    EXP (S Γ) ⊢ b ->
    EXP Γ ⊢ Seq e b
| ExpScoped_Op1 : forall o v,
    VAL Γ ⊢ v ->
    EXP Γ ⊢  Op1 o v
| ExpScoped_Op2 : forall o v1 v2,
    VAL Γ ⊢ v1 ->
    VAL Γ ⊢ v2 ->
    EXP Γ ⊢  Op2 o v1 v2
| ExpScoped_Cond : forall vp et ef,
    VAL Γ ⊢ vp ->
    EXP Γ ⊢ et ->
    EXP Γ ⊢ ef ->
    EXP Γ ⊢ Cond vp et ef
| ExpScoped_Sample : EXP Γ ⊢ Sample
| ExpScoped_Factor : forall v,
    VAL Γ ⊢ v ->
    EXP Γ ⊢ Factor v
| ExpScoped_Val : forall v,
    VAL Γ ⊢ v ->
    EXP Γ ⊢ v
with ValScoped (Γ : Env) : forall (e : Expr), Prop :=
| ValScoped_Var : forall n,
    n < Γ ->
    VAL Γ ⊢ Var n
| ValScoped_Const : forall r,
    VAL Γ ⊢ (Const r)
| ValScoped_Fun : forall (b : Expr),
    EXP (S Γ) ⊢ b ->
    VAL Γ ⊢ Fun b
where
"'EXP' Γ ⊢ e" := (ExpScoped Γ e)
and
"'VAL' Γ ⊢ e" := (ValScoped Γ e).

Hint Constructors ExpScoped.
Hint Constructors ValScoped.

Arguments ValScoped_Var {Γ} n Hlookup.
Arguments ValScoped_Const {Γ} r.
Arguments ValScoped_Fun {Γ} b Hb_scope.
Arguments ExpScoped_App {Γ} f v Hf_scope Hv_scope.
Arguments ExpScoped_Seq {Γ} e b He_scope Hb_scope.
Arguments ExpScoped_Op1 {Γ} o v Hv_scope.
Arguments ExpScoped_Op2 {Γ} o v1 v2 Hv1_scope Hv2_scope.
Arguments ExpScoped_Cond {Γ} vp et ef Hvp_scope Hvt_scope Hvf_scope.
Arguments ExpScoped_Sample {Γ}.
Arguments ExpScoped_Factor {Γ} v.

Notation "'ECLOSED' e" := (EXP 0%nat ⊢ e) (at level 69).
Notation "'VCLOSED' e" := (VAL 0%nat ⊢ e) (at level 69).

(** Helpers to automate proofs about scoping. *)
Ltac invert_scoped H :=
  match typeof H with 
  | VAL ?Γ ⊢ Var _ => inversion H; subst; clear H
  | VAL ?Γ ⊢ Fun ?b => inversion H; subst; clear H
  | VAL ?Γ ⊢ Const ?b => clear H
  | VAL ?Γ ⊢ _ => try solve [inversion H]

  | EXP ?Γ ⊢ Var _ => let H' := fresh in
                      inversion H as [ | | | | | | |? H'];
                      subst;
                      inversion H';
                      subst;
                      clear H H'
  | EXP ?Γ ⊢ Fun ?b => let H' := fresh in
                       inversion H as [ | | | | | | |? H'];
                       subst;
                       inversion H';
                       subst;
                       clear H H'
  | EXP ?Γ ⊢ Const ?b => clear H
  | EXP ?Γ ⊢ App ?f ?v =>
    inversion H; subst; clear H;
    [|match goal with
      | [ H' : VAL _ ⊢ App f v |- _] => inversion H'
      end]
  | EXP ?Γ ⊢ Op1 ?o ?v =>
    inversion H; subst; clear H;
    [|match goal with
      | [ H' : VAL _ ⊢ Op1 o v |- _] => inversion H'
      end]
  | EXP ?Γ ⊢ Op2 ?o ?v1 ?v2 =>
    inversion H; subst; clear H;
    [|match goal with
      | [ H' : VAL _ ⊢ Op2 o v1 v2 |- _] => inversion H'
      end]
  | EXP ?Γ ⊢ Cond ?p ?t ?f =>
    inversion H; subst; clear H;
    [|match goal with
      | [ H' : VAL _ ⊢ Cond p t f |- _] => inversion H'
      end]
  | EXP ?Γ ⊢ Seq ?x ?b =>
    inversion H; subst; clear H;
    [|match goal with
      | [ H' : VAL _ ⊢ Seq x b |- _] => inversion H'
      end]
  | EXP ?Γ ⊢ Sample =>
    inversion H; subst; clear H;
    [|match goal with
      | [ H' : VAL _ ⊢ Sample |- _] => inversion H'
      end]
  | EXP ?Γ ⊢ Factor ?r =>
    inversion H; subst; clear H;
    [|match goal with
      | [ H' : VAL _ ⊢ Factor r |- _] => inversion H'
      end]
  end.

Lemma VScoped_Var : forall Γ v,
    VAL Γ ⊢ Var v -> v < Γ.
Proof.
  intros.
  inversion H; subst.
  auto.
Qed.

Hint Resolve VScoped_Var.

Lemma EScoped_Var : forall Γ v,
    EXP Γ ⊢ Var v -> v < Γ.
Proof.
  intros.
  inversion H; subst.
  auto.
Qed.

Hint Resolve EScoped_Var.

Lemma EScoped_Fun :
  forall (b : Expr) (Γ : Env),
    EXP Γ ⊢ Fun b ->
    EXP S Γ ⊢ b.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  auto.
Qed.

Hint Resolve EScoped_Fun.

Lemma EScoped_App :
  forall (e1 e2 : Expr) (Γ : Env),
    EXP Γ ⊢ App e1 e2 ->
    VAL Γ ⊢ e1 /\ VAL Γ ⊢ e2.
Proof.
  intros.
  inversion H;
    subst;
    intuition.
Qed.

Lemma EScoped_App_f :
  forall (e1 e2 : Expr) (Γ : Env),
    EXP Γ ⊢ App e1 e2 ->
    VAL Γ ⊢ e1.
Proof.
  intros.
  apply EScoped_App in H.
  intuition.
Qed.

Hint Resolve EScoped_App_f.

Lemma EScoped_App_v :
  forall (e1 e2 : Expr) (Γ : Env),
    EXP Γ ⊢ App e1 e2 ->
    VAL Γ ⊢ e2.
Proof.
  intros.
  apply EScoped_App in H.
  intuition.
Qed.

Hint Resolve EScoped_App_v.

Lemma EScoped_Seq :
  forall (x : Expr) (b : Expr) (Γ : Env),
    EXP Γ ⊢ Seq x b ->
    (EXP Γ ⊢ x /\ EXP S Γ ⊢ b).
Proof.
  intros.
  inversion H;
    intuition.
Qed.

Lemma EScoped_Seq_x :
  forall (x : Expr) (b : Expr) (Γ : Env),
    EXP Γ ⊢ Seq x b -> EXP Γ ⊢ x.
Proof.
  intros.
  apply EScoped_Seq in H.
  intuition.
Qed.

Hint Resolve EScoped_Seq_x.

Lemma EScoped_Seq_b :
  forall (e : Expr) (b : Expr) (Γ : Env),
    EXP Γ ⊢ Seq e b -> EXP (S Γ) ⊢ b.
Proof.
  intros.
  apply EScoped_Seq in H.
  intuition.
Qed.

Hint Resolve EScoped_Seq_b.

Lemma EScoped_Op1 :
  forall (o : EOp1) (v : Expr) (Γ : Env),
    EXP Γ ⊢ Op1 o v -> VAL Γ ⊢ v.
Proof.
  intros.
  inversion H;
    intuition.
Qed.

Hint Resolve EScoped_Op1.

Lemma EScoped_Op2 :
  forall (o : EOp2) (v1 v2 : Expr) (Γ : Env),
    EXP Γ ⊢ Op2 o v1 v2 -> VAL Γ ⊢ v1 /\ VAL Γ ⊢ v2.
Proof.
  intros.
  inversion H;
    intuition.
Qed.

Lemma EScoped_Op2_lhs :
  forall (o : EOp2) (v1 v2 : Expr) (Γ : Env),
    EXP Γ ⊢ Op2 o v1 v2 -> VAL Γ ⊢ v1.
Proof.
  intros.
  apply EScoped_Op2 in H.
  intuition.
Qed.

Hint Resolve EScoped_Op2_lhs.

Lemma EScoped_Op2_rhs :
  forall (o : EOp2) (v1 v2 : Expr) (Γ : Env),
    EXP Γ ⊢ Op2 o v1 v2 -> VAL Γ ⊢ v2.
Proof.
  intros.
  apply EScoped_Op2 in H.
  intuition.
Qed.

Hint Resolve EScoped_Op2_rhs.

Lemma EScoped_Cond :
  forall (vp et ef : Expr) (Γ : Env),
    EXP Γ ⊢ Cond vp et ef -> VAL Γ ⊢ vp /\ EXP Γ ⊢ et /\ EXP Γ ⊢ ef.
Proof.
  intros.
  inversion H;
    intuition.
Qed.

Lemma EScoped_Cond_predicate :
  forall (vp et ef : Expr) (Γ : Env),
    EXP Γ ⊢ Cond vp et ef -> VAL Γ ⊢ vp.
Proof.
  intros.
  apply EScoped_Cond in H.
  intuition.
Qed.

Hint Resolve EScoped_Cond_predicate.

Lemma EScoped_Cond_true :
  forall (vp et ef : Expr) (Γ : Env),
    EXP Γ ⊢ Cond vp et ef -> EXP Γ ⊢ et.
Proof.
  intros.
  apply EScoped_Cond in H.
  intuition.
Qed.

Hint Resolve EScoped_Cond_true.

Lemma EScoped_Cond_false :
  forall (vp et ef : Expr) (Γ : Env),
    EXP Γ ⊢ Cond vp et ef -> EXP Γ ⊢ ef.
Proof.
  intros.
  apply EScoped_Cond in H.
  intuition.
Qed.

Hint Resolve EScoped_Cond_false.

Lemma EScoped_Factor :
  forall (v : Expr) (Γ : Env), EXP Γ ⊢ Factor v -> VAL Γ ⊢ v.
Proof.
  intros.
  inversion H;
    intuition.
Qed.

Hint Resolve EScoped_Factor.

(* Scope checking *)
Lemma Scoped_dec : forall e Γ,
    (ExpScoped Γ e \/ ~ ExpScoped Γ e) /\
    (ValScoped Γ e \/ ~ ValScoped Γ e).
Proof.
  induction e;
    intros;
    repeat
      match goal with
      | [ b : {bind Expr} |- _ ] =>
        match goal with
        | [ IHe : forall Γ : Env, (EXP Γ ⊢ b \/ ~ EXP Γ ⊢ b) /\
                                  (VAL Γ ⊢ b \/ ~ VAL Γ ⊢ b) |- _ ] =>
          specialize (IHe (S Γ));
            destruct IHe as [[|][|]]
        end
      | [ e : Expr |- _ ] =>
        match goal with
        | [ IHe : forall Γ : Env, (EXP Γ ⊢ e \/ ~ EXP Γ ⊢ e) /\
                                  (VAL Γ ⊢ e \/ ~ VAL Γ ⊢ e) |- _ ] =>
          specialize (IHe Γ);
            destruct IHe as [[|][|]]
        end
      end;
    split;
    try solve
        [match goal with
         | [ H : ~ EXP _ ⊢ _ |- _ ] =>
           right; contradict H; inversion H; subst; auto 2
         | [ H : ~ VAL _ ⊢ _ |- _ ] =>
           right; contradict H; inversion H; subst; auto 2
         | [ |- context[Var _] ]  =>
           destruct (lt_dec v Γ); intuition auto
         end
        |right; let H := fresh in intro H; inversion H
        |left; constructor; assumption
        |left; constructor; constructor; assumption].
Qed.

Lemma ValScoped_dec : forall e Γ, (decidable (ValScoped Γ e)).
Proof.
  apply Scoped_dec.
Qed.

Lemma succ_Scoped : forall {e Γ},
    (EXP Γ ⊢ e -> EXP S Γ ⊢ e) /\
    (VAL Γ ⊢ e -> VAL S Γ ⊢ e).
Proof.
  induction e;
    split;
    intros;
    try solve [inversion H; subst;
               inversion H0; subst;
               constructor;
               constructor;
               firstorder
              |inversion H; subst;
               constructor;
               firstorder].
Qed.

Lemma succ_ExpScoped : forall {e Γ},
    EXP Γ ⊢ e -> EXP S Γ ⊢ e.
Proof.
  intros.
  apply succ_Scoped.
  auto.
Qed.

Lemma succ_ValScoped : forall {e Γ},
    VAL Γ ⊢ e -> VAL S Γ ⊢ e.
Proof.
  intros.
  apply succ_Scoped.
  auto.
Qed.

Definition SubScoped (Γ : Env) (Γ' : Env) (γ : var -> Expr) : Prop :=
  forall v,
    v < Γ ->
    ValScoped Γ' (γ v).

Notation "'SUBSCOPE' Γ ⊢ γ ∷ Γ'" := (SubScoped Γ Γ' γ)
         (at level 69, γ at level 99, no associativity).

Definition RenScoped (Γ : Env) (Γ' : Env) (ξ : var -> var) : Prop :=
  forall v, v < Γ -> (ξ v) < Γ'.

Notation "'RENSCOPE' Γ ⊢ ξ ∷ Γ'" := (RenScoped Γ Γ' ξ)
         (at level 69, ξ at level 99, no associativity).

Lemma renscope_id Γ : RENSCOPE Γ ⊢ id ∷ Γ.
Proof.
  firstorder.
Qed.

Hint Resolve renscope_id.

Lemma scope_ids Γ : SUBSCOPE Γ ⊢ ids ∷ Γ.
Proof.
  firstorder.
Qed.

Hint Resolve scope_ids.

Lemma renup_scope : forall Γ Γ' ξ,
  RENSCOPE Γ ⊢ ξ ∷ Γ' ->
  RENSCOPE (S Γ) ⊢ upren ξ ∷ (S Γ').
Proof.
  intros.
  unfold RenScoped in *.
  intros.
  revert ξ Γ Γ' H H0.
  induction v;
    intros;
    asimpl;
    firstorder using Nat.succ_lt_mono.
Qed.

Hint Resolve renup_scope.

Lemma ren_preserves_scope : forall e Γ,
    (EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e) /\
    (VAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ rename ξ e).
Proof.
  induction e;
    intros Γ;
    split;
    split;
    intros;
    try solve
        [match goal with
         | [H : forall (Γ' : Env) (ξ : var -> var), RENSCOPE Γ ⊢ ξ ∷ Γ' -> _ |- _] =>
           specialize (H _ _ (renscope_id Γ));
             asimpl in H;
             assumption
         end];
    try invert_scoped H;
    try solve
        [constructor;
         let e := match goal with
                    | [ |- context[rename ?ξ ?e]] => e
                    end in
         match goal with
         | [IHe : forall (Γ : Env), (EXP Γ ⊢ e <-> _) /\ (VAL Γ ⊢ e <-> _),
              H : VAL _ ⊢ e |- _ ] =>
           eapply IHe in H; try eassumption; auto
         | [IHe : forall (Γ : Env), (EXP Γ ⊢ e <-> _) /\ (VAL Γ ⊢ e <-> _),
              H : EXP _ ⊢ e |- _ ] =>
           eapply IHe in H; try eassumption; auto
         end
        |do 2 (constructor; auto)];
    auto.
  do 2 constructor.
  eapply IHe in H3; eauto.
Qed.

Lemma ren_preserves_scope_exp : forall e Γ,
    (EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e).
Proof.
  intros.
  apply ren_preserves_scope.
Qed.

Lemma ren_preserves_scope_val : forall e Γ,
    (VAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ rename ξ e).
Proof.
  intros.
  apply ren_preserves_scope.
Qed.

Lemma up_val : forall Γ v γ,
  VAL Γ ⊢ γ v ->
  VAL S Γ ⊢ up γ (S v).
Proof.
  intros.
  asimpl.
  rewrite <- rename_subst.
  apply -> ren_preserves_scope_val; eauto.
  unfold RenScoped.
  intros.
  cbn.
  auto.
Qed.

Lemma up_scope : forall Γ Γ' γ,
  SUBSCOPE Γ ⊢ γ ∷ Γ' ->
  SUBSCOPE (S Γ) ⊢ up γ ∷ (S Γ').
Proof.
  intros.
  unfold SubScoped in *.
  intros.
  destruct v; intros.
  - constructor.
    auto.
  - asimpl; rewrite <- rename_subst.
    apply ren_preserves_scope_val with (Γ:= Γ').
    + destruct (H v); auto.
    + firstorder.
Qed.

Hint Resolve up_scope.

Lemma cons_scope : forall v Γ Γ' γ,
    VAL Γ' ⊢ v ->
    SUBSCOPE Γ ⊢ γ ∷ Γ' ->
    SUBSCOPE (S Γ) ⊢ v.:γ ∷ Γ'.
Proof.
  intros.
  unfold SubScoped in *.
  intros v' Hv'.
  destruct v';
    firstorder idtac using lt_S_n.
Qed.

Hint Resolve cons_scope.

(** Substitution is scope-preserving. *)
Lemma sub_preserves_scope : forall e Γ,
    (EXP Γ ⊢ e <->
     forall Γ' γ,
       SUBSCOPE Γ ⊢ γ ∷ Γ' ->
       EXP Γ' ⊢ e.[γ]) /\
    (VAL Γ ⊢ e <->
     forall Γ' γ,
       SUBSCOPE Γ ⊢ γ ∷ Γ' ->
       VAL Γ' ⊢ e.[γ]).
Proof.
  induction e;
    intros Γ;
    split;
    split;
    intros;
    try solve
        [match goal with
         | [H : forall (Γ' : Env) (γ : var -> Expr), SUBSCOPE Γ ⊢ γ ∷ Γ' -> _ |- _] =>
           specialize (H _ _ (scope_ids Γ));
             asimpl in H;
             assumption
         end];
    try invert_scoped H;
    try solve
        [constructor;
         let e := match goal with
                  | [ |- context[?e.[?γ]]] => e
                  end in
         match goal with
         | [IHe : forall (Γ : Env), (EXP Γ ⊢ e <-> _) /\ (VAL Γ ⊢ e <-> _),
              H : VAL _ ⊢ e |- _ ] =>
           eapply IHe in H; try eassumption; auto
         | [IHe : forall (Γ : Env), (EXP Γ ⊢ e <-> _) /\ (VAL Γ ⊢ e <-> _),
              H : EXP _ ⊢ e |- _ ] =>
           eapply IHe in H; try eassumption; auto
         end];
    auto.
  - constructor.
    apply H0.
    auto.
  - apply H0.
    auto.
  - do 2 constructor.
  - do 2 constructor.
    eapply IHe in H3; eauto.
Qed.

Lemma sub_preserves_scope_exp : forall e Γ,
    EXP Γ ⊢ e <->
    forall Γ' γ,
      SUBSCOPE Γ ⊢ γ ∷ Γ' ->
      EXP Γ' ⊢ e.[γ].
Proof.
  intros.
  apply sub_preserves_scope.
Qed.

Lemma sub_preserves_scope_val : forall e Γ,
    VAL Γ ⊢ e <->
    forall Γ' γ,
      SUBSCOPE Γ ⊢ γ ∷ Γ' ->
      VAL Γ' ⊢ e.[γ].
Proof.
  intros.
  apply sub_preserves_scope.
Qed.

Module SUB_IMPLIES_SCOPE.
  Definition magic_γ (Γ Γ' : Env) (n : nat) :=
    if lt_dec n Γ
    then if lt_dec n Γ'
         then Var n
         else Const 0
    else Var Γ'.

  Lemma magic_γ_scope : forall Γ Γ', SUBSCOPE Γ ⊢ magic_γ Γ Γ' ∷ Γ'.
  Proof.
    unfold SubScoped.
    intros.
    unfold magic_γ, pred.
    repeat destruct lt_dec;
      auto.
  Qed.

  Lemma up_magic Γ Γ': up (magic_γ Γ Γ') = magic_γ (S Γ) (S Γ').
  Proof.
    extensionality x.
    unfold magic_γ, up.
    destruct x; cbn; auto.
    repeat destruct lt_dec; auto.
  Qed.

  Lemma magic_γ_implies_scope : forall e Γ Γ',
      (EXP Γ' ⊢ e.[magic_γ Γ Γ'] ->
       EXP Γ ⊢ e) /\
      (VAL Γ' ⊢ e.[magic_γ Γ Γ'] ->
       VAL Γ ⊢ e).
  Proof.
    induction e;
      intros Γ Γ';
      split;
      intros;
      cbn in H;
      try invert_scoped H;
      try solve
          [constructor;
           let e := match goal with
                    | [ |- EXP _ ⊢ ?e ] => e
                    | [ |- VAL _ ⊢ ?e ] => e
                    end in
           match goal with
           | [IHe : forall (Γ Γ' : Env), (_ -> EXP Γ ⊢ e) /\ (_ -> VAL Γ ⊢ e),
                H : VAL _ ⊢ e.[magic_γ Γ Γ'] |- _ ] =>
             eapply IHe in H; try eassumption; auto
           | [IHe : forall (Γ Γ' : Env), (_ -> EXP Γ ⊢ e) /\ (_ -> VAL Γ ⊢ e),
                H : EXP _ ⊢ e.[magic_γ Γ Γ'] |- _ ] =>
             eapply IHe in H; try eassumption; auto
           end];
    auto.
    - cbn in *.
      unfold magic_γ in H.
      repeat destruct lt_dec;
        auto.
      inversion H; subst.
      inversion H0.
      auto.
    - cbn in *.
      unfold magic_γ in H.
      repeat destruct lt_dec;
        auto.
      inversion H.
      auto.
    - constructor.
      constructor.
      eapply IHe.
      rewrite <- up_magic.
      eauto.
    - constructor.
      eapply IHe.
      rewrite <- up_magic.
      eauto.
    - constructor;
        firstorder idtac.
      eapply IHe0.
      rewrite <- up_magic.
      eauto.
  Qed.

  Lemma sub_implies_scope_exp : forall e Γ Γ',
      (forall γ, SUBSCOPE Γ ⊢ γ ∷ Γ' -> EXP Γ' ⊢ e.[γ]) ->
      EXP Γ ⊢ e.
  Proof.
    intros;
    eapply magic_γ_implies_scope;
    apply H;
    apply magic_γ_scope.
  Qed.

  Lemma sub_implies_scope_val : forall e Γ Γ',
      (forall γ, SUBSCOPE Γ ⊢ γ ∷ Γ' -> VAL Γ' ⊢ e.[γ]) ->
      VAL Γ ⊢ e.
  Proof.
    intros;
    eapply magic_γ_implies_scope;
    apply H;
    apply magic_γ_scope.
  Qed.

  Definition magic_γ_2 Γ' :=
    fun n =>
      if lt_dec n Γ'
      then Var n
      else if Nat.eq_dec n Γ'
           then Const 0
           else Var (pred n).

  Lemma up_magic_2 : forall Γ,
      up (magic_γ_2 Γ) = magic_γ_2 (S Γ).
  Proof.
    intros.
    unfold magic_γ_2.
    extensionality x.
    unfold up.
    unfold ".:".
    destruct x; auto.
    simpl.
    unfold Init.Nat.pred.
    repeat destruct lt_dec;
      destruct (Nat.eq_dec x Γ);
      destruct x;
      subst;
      cbn;
      auto.
  Qed.

  Lemma magic_const : magic_γ_2 0 = Const 0 .: ids.
  Proof.
    unfold magic_γ_2.
    extensionality x.
    destruct lt_dec; auto.
    destruct Nat.eq_dec; subst; auto.
    destruct x; cbn; auto.
  Qed.

  Lemma foo : forall e Γ',
      (EXP Γ' ⊢ e.[magic_γ_2 Γ'] ->
       e.[magic_γ (S Γ') Γ'] = e.[magic_γ_2 Γ']) /\
      (VAL Γ' ⊢ e.[magic_γ_2 Γ'] ->
       e.[magic_γ (S Γ') Γ'] = e.[magic_γ_2 Γ']).
  Proof.
    induction e;
      split;
      intros Hscope;
      cbn;
      cbn in Hscope;
      try invert_scoped Hscope;
      auto;
      try rewrite up_magic_2 in *;
      try rewrite up_magic in *;
      try solve
          [repeat
             match goal with
             | [ IHe : forall (Γ' : Env), (EXP Γ' ⊢ ?e.[_] -> _) /\ (VAL Γ' ⊢ ?e.[_] -> _),
                   H : VAL _ ⊢ ?e.[_]
                   |- _] => apply IHe in H
             | [ IHe : forall (Γ' : Env), (EXP Γ' ⊢ ?e.[_] -> _) /\ (VAL Γ' ⊢ ?e.[_] -> _),
                   H : EXP _ ⊢ ?e.[_]
                   |- _] => apply IHe in H
             end;
           f_equal;
           auto].
    - unfold magic_γ, magic_γ_2 in *;
        cbn in *;
        repeat destruct lt_dec; auto;
          destruct (Nat.eq_dec v Γ'); auto;
            destruct v, Γ';
            inversion Hscope;
            try inversion H;
            subst;
            cbn;
            auto.
    - asimpl in Hscope.
      unfold magic_γ, magic_γ_2 in *.
      repeat destruct lt_dec;
        repeat destruct Nat.eq_dec;
        inversion Hscope;
        auto.
  Qed.

  Lemma bar : forall e,
      (ECLOSED e.[Const 0/] ->
       e.[magic_γ 1 0] = e.[Const 0 .: ids]) /\
      (VCLOSED e.[Const 0/] ->
       e.[magic_γ 1 0] = e.[Const 0 .: ids]).
  Proof.
    intros.
    rewrite <- magic_const.
    apply foo.
  Qed.

  Lemma sub_implies_scope_exp_1 : forall e,
      ECLOSED e.[Const 0/] ->
      EXP 1 ⊢ e.
  Proof.
    intros;
      eapply magic_γ_implies_scope.
    destruct (bar e).
    rewrite H0; auto.
  Qed.

  Lemma sub_implies_scope_val_1 : forall e,
      VCLOSED e.[Const 0/] ->
      VAL 1 ⊢ e.
  Proof.
    intros;
      eapply magic_γ_implies_scope.
    destruct (bar e).
    rewrite H1; auto.
  Qed.
End SUB_IMPLIES_SCOPE.

Definition sub_implies_scope_exp := SUB_IMPLIES_SCOPE.sub_implies_scope_exp.
Definition sub_implies_scope_val := SUB_IMPLIES_SCOPE.sub_implies_scope_val.
Definition sub_implies_scope_exp_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_exp_1.
Definition sub_implies_scope_val_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_val_1.

Lemma upn_Var : forall (Γ : Env) (γ : var -> Expr) (v : var),
    v < Γ -> upn Γ γ v = Var v.
Proof.
  intros Γ γ.
  induction Γ;
    intros.
  + auto.
  + rewrite iterate_S.
    destruct v;
      asimpl;
      auto.
    rewrite IHΓ;
      auto.
Qed.

Lemma scoped_ignores_sub : forall e Γ γ,
     (EXP Γ ⊢ e -> e.[upn Γ γ] = e) /\
     (VAL Γ ⊢ e -> e.[upn Γ γ] = e).
Proof.
  induction e;
    cbn;
    split;
    intros;
    invert_scoped H;
    auto using upn_Var;
    try solve
        [repeat
           match goal with
           | [ IHe : forall (Γ : Env) (γ : var -> Expr), (EXP Γ ⊢ ?e -> _) /\ (VAL Γ ⊢ ?e -> _),
                 H : VAL _ ⊢ ?e
                 |- _] => eapply IHe in H
           | [ IHe : forall (Γ : Env) (γ : var -> Expr), (EXP Γ ⊢ ?e -> _) /\ (VAL Γ ⊢ ?e -> _),
                 H : EXP _ ⊢ ?e
                 |- _] => eapply IHe in H
           end;
         f_equal;
         eauto].
Qed.

Lemma escoped_ignores_sub : forall e Γ γ,
    EXP Γ ⊢ e -> e.[upn Γ γ] = e.
Proof.  
  intros.
  eapply scoped_ignores_sub in H.
  eauto.
Qed.
Hint Resolve escoped_ignores_sub.

Lemma vscoped_ignores_sub : forall e Γ γ,
    VAL Γ ⊢ e -> e.[upn Γ γ] = e.
Proof.
  intros.
  eapply scoped_ignores_sub in H.
  eauto.
Qed.
Hint Resolve vscoped_ignores_sub.

Lemma eclosed_ignores_sub : forall e γ,
     ECLOSED e -> e.[γ] = e.
Proof.
  intros.
  replace (e.[γ]) with (e.[upn 0 γ])
    by (rewrite upn0; auto).
  auto.
Qed.
Hint Resolve eclosed_ignores_sub.

Lemma vclosed_ignores_sub : forall e γ,
     VCLOSED e -> e.[γ] = e.
Proof.
  intros.
  replace (e.[γ]) with (e.[upn 0 γ])
    by (rewrite upn0; auto).
  auto.
Qed.
Hint Resolve vclosed_ignores_sub.

Lemma eclosed_sub_closed : forall v γ,
    ECLOSED v -> ECLOSED v.[γ].
Proof.
  intros.
  rewrite eclosed_ignores_sub;
    auto.
Qed.
Hint Resolve eclosed_sub_closed.

Lemma vclosed_sub_closed : forall v γ,
    VCLOSED v -> VCLOSED v.[γ].
Proof.
  intros.
  rewrite vclosed_ignores_sub;
    auto.
Qed.
Hint Resolve vclosed_sub_closed.

(* Continuations *)

Inductive Kont : Type :=
| Knil : forall (A : Measurable R), Kont
| Kcons : Expr -> Kont -> Kont.

Infix "-:" := Kcons (at level 60, right associativity).

Lemma Kont_eq_dec : forall (K K' : Kont),
    decidable (K = K').
Proof.
  unfold decidable.
  induction K;
    destruct K';
    intros;
    try solve [intuition auto].
  - destruct (Measurable_R_eq_dec A A0).
    + subst.
      intuition.
    + right.
      contradict H.
      inversion H; auto.
  - destruct (Expr_eq_dec e e0);
      subst;
      revgoals.
    { right.
      contradict n.
      inversion n; subst; auto.
    }
    specialize (IHK K').
    inversion IHK; subst.
    + left; auto.
    + right.
      contradict H.
      inversion H.
      auto.
Qed.

Reserved Notation "'KCLOSED' K" (at level 69).

Inductive KontScoped : forall K, Prop :=
| KontScoped_nil : forall A,
    KCLOSED Knil A
| KontScoped_cons : forall K e,
    EXP 1 ⊢ e ->
    KCLOSED K ->
    KCLOSED e -: K
where
"'KCLOSED' K" := (KontScoped K).

Hint Constructors KontScoped.
