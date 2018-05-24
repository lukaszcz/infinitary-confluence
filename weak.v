Require Export beta.

Lemma lem_red_wh_refl : forall x y, x == y -> red_wh x y.
Proof.
  unfold red_wh; pose_star; ycrush.
Qed.

Lemma lem_red_wh_refl_0 : reflexive term red_wh.
Proof.
  unfold red_wh; pose_star; ycrush.
Qed.

Lemma lem_step_wh_morphism : morphism step_wh.
Proof.
  unfold morphism.
  induction 1.
  - inversion H; subst; constructor.
    rewrite H2 in *; rewrite H3 in *.
    assumption.
  - intros x0 y0 H1 H2.
    inversion H1; inversion H2; subst; yisolve.
    fold term_eq in *.
    rewrite H7 in *.
    ycrush.
Qed.

Lemma lem_star_n_step_wh_morphism : forall n, morphism (star_n step_wh n).
Proof.
  unfold red_wh.
  apply lem_star_n_morphism.
  apply lem_step_wh_morphism.
Qed.

Lemma lem_red_wh_morphism : morphism red_wh.
Proof.
  unfold red_wh.
  apply lem_star_morphism.
  apply lem_step_wh_morphism.
Qed.

Lemma lem_inf_wh_morphism : morphism inf_wh.
Proof.
  unfold inf_wh.
  apply lem_inf_morphism.
  apply lem_step_wh_morphism.
Qed.

Add Parametric Morphism : step_wh with
    signature term_eq ==> term_eq ==> iff as step_wh_mor.
Proof.
  split; intro; eapply lem_step_wh_morphism; pose_term_eq; eauto.
Qed.

Add Parametric Morphism (n : nat) : (star_n step_wh n) with
    signature term_eq ==> term_eq ==> iff as star_n_step_wh_mor.
Proof.
  split; intro; eapply lem_star_n_step_wh_morphism; pose_term_eq; eauto.
Qed.

Add Parametric Morphism : red_wh with
    signature term_eq ==> term_eq ==> iff as red_wh_mor.
Proof.
  split; intro; eapply lem_red_wh_morphism; pose_term_eq; eauto.
Qed.

Add Parametric Morphism : inf_wh with
    signature term_eq ==> term_eq ==> iff as inf_wh_mor.
Proof.
  split; intro; eapply lem_inf_wh_morphism; pose_term_eq; eauto.
Qed.

Lemma lem_red_wh_trans : transitive term red_wh.
Proof.
  unfold red_wh, transitive; pose_star; pose lem_step_wh_morphism; ycrush.
Qed.

Lemma lem_red_wh_step : forall x y z, step_wh x y -> red_wh y z -> red_wh x z.
Proof.
  unfold red_wh; pose_star; ycrush.
Qed.

Lemma lem_red_wh_step_rev : forall x y z, red_wh x y -> step_wh y z -> red_wh x z.
Proof.
  unfold red_wh.
  intros x y z H.
  destruct H as [n H].
  revert z.
  induction H; pose_star; ycrush.
Qed.

Lemma lem_step_wh_redex : forall x y, step_wh (app (abs x) y) (x [0 := y]).
Proof.
  constructor; econstructor; pose_term_eq; eauto.
Qed.

Lemma lem_red_wh_redex : forall x y, red_wh (app (abs x) y) (x [0 := y]).
Proof.
  intros; econstructor; econstructor 2.
  - eauto using lem_step_wh_redex.
  - constructor; pose_term_eq; eauto.
Qed.

Lemma lem_step_wh_to_red_wh : forall x y, step_wh x y -> red_wh x y.
Proof.
  intros; econstructor; econstructor 2; eauto.
  econstructor; pose_term_eq; ycrush.
Qed.

Lemma lem_red_wh_app : forall x x' y, red_wh x x' -> red_wh (app x y) (app x' y).
Proof.
  intros x x' y H.
  destruct H as [n H].
  revert y.
  induction H; intro y0.
  - apply lem_red_wh_refl; pose_term_eq; ycrush.
  - assert (step_wh (app x y0) (app y y0)) by (pose_term_eq; ycrush).
    pose lem_red_wh_step; ycrush.
Qed.

Lemma lem_step_wh_to_step_beta : forall x y, step_wh x y -> step_beta x y.
Proof.
  induction 1; ycrush.
Qed.

Lemma lem_red_wh_to_red_beta : forall x y, red_wh x y -> red_beta x y.
Proof.
  intros x y H.
  destruct H as [n H].
  induction H.
  - ycrush.
  - pose lem_step_wh_to_step_beta; pose_star; pose lem_beta_redex_morphism;
      unfold red_beta in *; ycrush.
Qed.

Ltac pose_red_wh := pose proof lem_red_wh_refl_0; pose proof lem_red_wh_refl; pose proof lem_red_wh_trans;
                    pose proof lem_red_wh_step; pose proof lem_red_wh_step_rev;
                    pose proof lem_red_wh_redex; pose proof lem_step_wh_to_red_wh;
                    pose proof lem_red_wh_app; pose proof lem_red_wh_to_red_beta;
                    autounfold with shints in *.

(******************************************************************************)

Lemma lem_step_wh_shift_closed : shift_closed step_wh.
Proof.
  unfold shift_closed.
  induction 1.
  - assert (beta_redex (shift d c x) (shift d c y)) by
        (pose lem_beta_redex_shift_closed; scrush).
    constructor; assumption.
  - rewrite H0.
    autorewrite with shints.
    pose_term_eq; ycrush.
Qed.

Lemma lem_red_wh_shift_closed : shift_closed red_wh.
Proof.
  unfold red_wh.
  pose lem_step_wh_morphism; pose lem_star_shift_closed; pose lem_step_wh_shift_closed; scrush.
Qed.

Lemma lem_inf_wh_shift_closed : shift_closed inf_wh.
Proof.
  pose lem_inf_shift_closed; pose lem_red_wh_shift_closed; scrush.
Qed.

Lemma lem_step_wh_subst_closed : subst_closed step_wh.
Proof.
  unfold subst_closed.
  induction 1.
  - assert (beta_redex (x [n := y]) (y0 [n := y])) by (pose lem_beta_redex_subst_closed; scrush).
    constructor; assumption.
  - rewrite H0.
    autorewrite with shints.
    pose_term_eq; ycrush.
Qed.

Lemma lem_red_wh_subst_closed : subst_closed red_wh.
Proof.
  unfold red_wh.
  pose lem_step_wh_morphism; pose lem_star_subst_closed; pose lem_step_wh_subst_closed; scrush.
Qed.

Lemma lem_inf_wh_subst :
  forall s s' t t', inf_wh s s' -> inf_wh t t' ->
                    forall n, inf_wh (s [n := t]) (s' [n := t']).
Proof.
  unfold inf_wh; unfold red_wh.
  pose lem_step_wh_subst_closed; pose lem_step_wh_shift_closed; apply lem_inf_subst; auto.
  apply lem_step_wh_morphism.
Qed.

Lemma lem_inf_wh_refl_0 : reflexive term inf_wh.
Proof.
  unfold inf_wh, red_wh; pose lem_inf_refl_0; scrush.
Qed.

Lemma lem_inf_wh_subst_closed : subst_closed inf_wh.
Proof.
  unfold subst_closed.
  pose lem_inf_wh_subst; pose lem_inf_wh_refl_0; scrush.
Qed.

Lemma lem_inf_wh_prepend : forall x y z, red_wh x y -> inf_wh y z -> inf_wh x z.
Proof.
  unfold inf_wh, red_wh.
  pose lem_step_wh_morphism; pose lem_inf_prepend; eauto.
Qed.

Lemma lem_inf_wh_append_step_beta : forall t1 t2 t3, inf_wh t1 t2 -> step_beta t2 t3 -> inf_wh t1 t3.
Proof.
  intros t1 t2 t3 H0 H.
  revert t1 H0.
  induction H; intros t1 HH.
  - inversion H; subst.
    rewrite H0 in HH.
    rewrite H1.
    inversion HH; subst; fold inf_wh in *.
    inversion H6; subst; fold inf_wh in *.
    assert (red_wh t1 (x1 [0 := y0])) by
        (eauto using lem_red_wh_redex, lem_red_wh_app, lem_red_wh_trans).
    eauto using lem_inf_wh_subst, lem_inf_wh_prepend.
  - rewrite H0 in HH; inversion HH; subst; fold inf_wh in *.
    econstructor; fold inf_wh; eauto.
  - rewrite H0 in HH; inversion HH; subst; fold inf_wh in *.
    econstructor; fold inf_wh; eauto.
  - inversion HH; subst; fold inf_wh in *.
    econstructor; fold inf_wh; eauto.
Qed.

Lemma lem_inf_wh_append_red_beta : forall t1 t2 t3, inf_wh t1 t2 -> red_beta t2 t3 -> inf_wh t1 t3.
Proof.
  intros t1 t2 t3 H1 H2.
  revert t1 H1.
  destruct H2 as [n H].
  induction H; intros.
  - rewrite <- H; assumption.
  - pose lem_inf_wh_append_step_beta; eauto.
Qed.

Lemma lem_inf_wh_append_step_wh : forall t1 t2 t3, inf_wh t1 t2 -> step_wh t2 t3 -> inf_wh t1 t3.
Proof.
  pose lem_inf_wh_append_step_beta; pose lem_step_wh_to_step_beta; ycrush.
Qed.

Lemma lem_inf_wh_append_red_wh : forall t1 t2 t3, inf_wh t1 t2 -> red_wh t2 t3 -> inf_wh t1 t3.
Proof.
  pose lem_inf_wh_append_red_beta; pose lem_red_wh_to_red_beta; ycrush.
Qed.

Lemma lem_inf_wh_appendable : appendable red_wh.
Proof.
  unfold appendable; pose lem_inf_wh_append_red_wh; eauto.
Qed.

Lemma lem_inf_wh_trans : transitive term inf_wh.
Proof.
  eauto using lem_inf_trans, lem_inf_wh_appendable.
Qed.

Lemma lem_red_wh_to_inf_wh : forall x y, red_wh x y -> inf_wh x y.
Proof.
  unfold inf_wh, red_wh.
  eauto using lem_star_to_inf, lem_step_wh_morphism.
Qed.

Lemma lem_step_wh_to_inf_wh : forall x y, step_wh x y -> inf_wh x y.
Proof.
  eauto using lem_step_wh_to_red_wh, lem_red_wh_to_inf_wh.
Qed.

Lemma lem_inf_wh_app : forall x x' y y', inf_wh x x' -> inf_wh y y' -> inf_wh (app x y) (app x' y').
Proof.
  pose_red_wh; pose lem_inf_wh_refl_0; coinduction.
Qed.

Lemma lem_inf_wh_abs : forall x x', inf_wh x x' -> inf_wh (abs x) (abs x').
Proof.
  pose_red_wh; pose lem_inf_wh_refl_0; coinduction.
Qed.

Ltac pose_inf_wh := pose proof lem_inf_wh_refl_0; pose proof lem_inf_wh_trans; pose proof lem_step_wh_to_inf_wh;
                    pose proof lem_red_wh_to_inf_wh; pose proof lem_inf_wh_prepend;
                    pose proof lem_inf_wh_append_red_wh; pose proof lem_inf_wh_append_step_wh;
                    pose proof lem_inf_wh_append_red_beta; pose proof lem_inf_wh_append_step_beta;
                    pose proof lem_inf_wh_app; pose proof lem_inf_wh_abs;
                    autounfold with shints in *.

(******************************************************************************)

Definition aux_wh := aux_clos step_wh.
Hint Unfold aux_wh.

Lemma lem_aux_wh_to_inf_wh : forall x y, aux_wh x y -> inf_wh x y.
Proof.
  pose lem_aux_to_inf; pose lem_inf_wh_appendable; unfold inf_wh, red_wh in *; ycrush.
Qed.

Lemma lem_beta_redex_to_step_wh : forall x y, beta_redex x y -> step_wh x y.
Proof.
  ycrush.
Qed.

Lemma lem_step_beta_to_inf_wh : forall x y, step_beta x y -> inf_wh x y.
Proof.
  induction 1; pose lem_beta_redex_to_step_wh; pose_red_wh; pose_inf_wh; ycrush.
Qed.

Lemma lem_red_beta_to_inf_wh : forall x y, red_beta x y -> inf_wh x y.
Proof.
  intros x y H; destruct H as [n H]; induction H;
    pose lem_step_beta_to_inf_wh; pose_red_wh; pose_inf_wh; ycrush.
Qed.

Lemma lem_inf_beta_to_aux_wh : forall x y, inf_beta x y -> aux_wh x y.
Proof.
  pose lem_red_beta_to_inf_wh; coinduction.
Qed.

Lemma lem_inf_beta_to_inf_wh : forall x y, inf_beta x y -> inf_wh x y.
Proof.
  Reconstr.reasy (@lem_aux_wh_to_inf_wh, @lem_inf_beta_to_aux_wh) Reconstr.Empty.
Qed.

Lemma lem_inf_wh_to_inf_beta : forall x y, inf_wh x y -> inf_beta x y.
Proof.
  pose lem_red_wh_to_red_beta; coinduction.
Qed.

Theorem thm_standardization : forall x y, inf_beta x y <-> inf_wh x y.
Proof.
  Reconstr.reasy (@lem_inf_beta_to_inf_wh, @lem_inf_wh_to_inf_beta) Reconstr.Empty.
Qed.

Lemma lem_step_wh_not_abs : forall x y, ~(step_wh (abs x) y).
Proof.
  sauto.
Qed.

Lemma lem_red_wh_from_abs : forall x y, red_wh (abs x) y -> y == abs x.
Proof.
  enough (forall x y u, u = abs x -> red_wh u y -> y == abs x) by ycrush.
  intros x y u H1 H; destruct H as [n H]; induction H; pose lem_step_wh_not_abs; ycrush.
Qed.

Lemma lem_inf_wh_from_abs : forall x y, inf_wh (abs x) y -> exists z, y == abs z /\ inf_wh x z.
Proof.
  intros x y H.
  inversion_clear H; sintuition.
  - pose lem_red_wh_from_abs; ycrush.
  - pose lem_red_wh_from_abs; ycrush.
  - pose lem_red_wh_from_abs; ycrush.
  - assert (HH: abs x0 == abs x) by (pose lem_red_wh_from_abs; ycrush).
    inversion HH; sintuition; fold term_eq inf_wh in *.
    rewrite H3 in *.
    pose_term_eq; ycrush.
Qed.

Lemma lem_step_wh_unique : forall x y, step_wh x y -> forall z, step_wh x z -> y == z.
Proof.
  induction 1.
  - intros z H1; inversion H1; sauto.
    + rewrite H2 in *.
      inversion H0; sintuition; fold term_eq in *.
      inversion H7; sintuition; fold term_eq in *.
      rewrite H9 in *; rewrite H6 in *.
      pose_term_eq; ycrush.
    + inversion H3; pose lem_step_wh_not_abs; ycrush.
  - intros z H1; inversion H1; sauto.
    + inversion H3; pose lem_step_wh_not_abs; ycrush.
    + pose_term_eq; ycrush.
Qed.

Lemma lem_star_n_step_wh_unique : forall n x y z, star_n step_wh n x y -> star_n step_wh n x z -> y == z.
Proof.
  induction n.
  - pose lem_step_wh_unique; scrush.
  - sauto.
    assert (HH: y0 == y1) by (pose lem_step_wh_unique; scrush).
    rewrite HH in *; clear HH.
    eauto.
Qed.

Definition step_wh_eq x y := step_wh x y \/ x == y.
Hint Unfold step_wh_eq.

Lemma lem_red_wh_rev : forall t s, red_wh t s -> (exists u, step_wh t u /\ red_wh u s) \/ t == s.
Proof.
  intros t s H.
  destruct H as [n H]; inversion H; subst; [ right; pose_term_eq; ycrush | left; ycrush ].
Qed.
