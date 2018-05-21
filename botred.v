
Require Import beta.

Section Botred.

Variable U : term -> Prop.
Variable Hm : meaningless U.

Lemma lem_par_bot_refl_0 : forall x, par_bot U x x.
Proof.
  coinduction on 0.
Qed.

Lemma lem_par_bot_refl : forall x y, x == y -> par_bot U x y.
Proof.
  coinduction.
Qed.

Lemma lem_U_morphism : forall x y, U x -> x == y -> U y.
Proof.
  intros.
  assert (inf_beta x y) by (pose_inf_beta; ycrush).
  sauto.
Qed.

Lemma lem_bot_redex_morphism : morphism (bot_redex U).
Proof.
  unfold morphism, bot_redex.
  pose lem_U_morphism; pose_term_eq; ycrush.
Qed.

Lemma lem_par_bot_morphism : morphism (par_bot U).
Proof.
  unfold morphism.
  coinduction CH using auto.
  - clear CH; pose lem_bot_redex_morphism; ycrush.
  - revert H; csolve CH.
  - revert H; csolve CH.
  - intros x1 y1 Ha1 Ha2;
      inversion Ha1; subst; try solve [ clear CH; exfalso; auto ];
        inversion Ha2; subst; try solve [ clear CH; exfalso; auto ].
    fold term_eq in *.
    constructor 4.
    + apply CH with (x := x0) (y := x'); pose_term_eq; eauto.
    + pose_term_eq; ycrush.
  - clear H0; revert H; csolve CH.
    clear CH; sauto.
Qed.

Add Parametric Morphism : (bot_redex U) with
    signature term_eq ==> term_eq ==> iff as bot_redex_mor.
Proof.
  split; intro; eapply lem_bot_redex_morphism; pose_term_eq; eauto.
Qed.

Add Parametric Morphism : (par_bot U) with
    signature term_eq ==> term_eq ==> iff as par_bot_mor.
Proof.
  split; intro; eapply lem_par_bot_morphism; pose_term_eq; eauto.
Qed.

Lemma lem_bot_redex_shift_closed : shift_closed (bot_redex U).
Proof.
  unfold shift_closed, bot_redex.
  sintuition.
  - sauto.
  - destruct t; autorewrite with shints in *; pose_term_eq; yelles 1.
  - rewrite H2; autorewrite with shints in *; yelles 1.
Qed.

Lemma lem_par_bot_shift_closed : shift_closed (par_bot U).
Proof.
  pose lem_bot_redex_shift_closed; unfold shift_closed.
  coinduction.
Qed.

Lemma lem_bot_redex_subst : forall t t' s s', bot_redex U t t' ->
                                              forall n, bot_redex U (t[n := s]) (t'[n := s']) \/
                                                        (t = var n /\ s == bot).
Proof.
  unfold bot_redex.
  intros; simp_hyps.
  assert (Hr1: U (t [n := s])) by sauto.
  assert (Hr3: t' [n := s'] == bot) by (rewrite H1; autorewrite with shints in *; yelles 1).
  destruct t eqn:?; autorewrite with shints in *; try solve [ pose_term_eq; left; yelles 1 ].
  repeat ysplit.
  - left; sauto.
  - destruct s eqn:?; autorewrite with shints in *; try solve [ pose_term_eq; left; yelles 1 ].
    right; split.
    + bomega.
    + reflexivity.
  - left; sauto.
Qed.

Lemma lem_par_bot_subst : forall t t' s s', par_bot U t t' -> par_bot U s s' ->
                                            forall n, par_bot U (t [n := s]) (t' [n := s']).
Proof.
  coinduction CH using auto.
  - clear CH; intros.
    generalize (lem_bot_redex_subst t t' s s' H0 n).
    sintuition.
    + yelles 1.
    + assert (HH: t' == bot) by ycrush.
      rewrite HH.
      rewrite H4.
      autorewrite with shints; repeat ysplit; try bomega.
      ycrush.
  - clear CH; intros; autorewrite with shints; repeat ysplit; try bomega.
    + eauto using lem_par_bot_refl_0.
    + eauto using lem_par_bot_shift_closed.
  - revert H; csolve CH.
  - revert H; csolve CH.
Qed.

End Botred.
