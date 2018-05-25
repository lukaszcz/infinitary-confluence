
Require Import weak.

Inductive is_var_app (n : nat) : term -> Prop :=
| is_var_app_var : forall t, t == var n -> is_var_app n t
| is_var_app_app : forall t u, is_var_app n t -> is_var_app n (app t u).

CoInductive succ (n : nat) : term -> term -> Prop :=
| succ_base : forall t s, is_var_app n s -> succ n t s
| succ_bot : succ n bot bot
| succ_var : forall m, succ n (var m) (var m)
| succ_app : forall t t' s s', succ n t t' -> succ n s s' -> succ n (app t s) (app t' s')
| succ_abs : forall t t', succ (n + 1) t t' -> succ n (abs t) (abs t').

Add Parametric Morphism (n : nat) : (is_var_app n)  with
    signature term_eq ==> iff as is_var_app_mor.
Proof.
  split.
  intro HH; revert y H; induction HH; pose_term_eq; ycrush.
  intro HH; revert x H; induction HH; pose_term_eq; ycrush.
Qed.

Lemma lem_succ_morphism : forall n, morphism (succ n).
Proof.
  unfold morphism.
  coinduction CH.
  - clear CH; intros x' y' HH1 HH2.
    rewrite HH2 in *.
    ycrush.
  - intros x' y' HH1 HH2.
    inversion_clear HH1; inversion_clear HH2; subst; yisolve; fold term_eq in *.
    apply succ_app; eapply CH; clear CH; cycle 1; eauto.
Qed.

Add Parametric Morphism (n : nat) : (succ n)  with
    signature term_eq ==> term_eq ==> iff as succ_mor.
Proof.
  split; intro; eapply lem_succ_morphism; pose_term_eq; eauto.
Qed.

Lemma lem_is_var_app_subst : forall n t, is_var_app (n + 1) t ->
                                         forall m s, m <= n -> is_var_app n (t [m := s]).
Proof.
  induction 1; intros.
  - rewrite H; clear H.
    autorewrite with shints; repeat ysplit; try bomega.
    assert (HH: n + 1 - 1 = n) by omega.
    rewrite HH; clear HH.
    pose_term_eq; ycrush.
  - autorewrite with shints.
    constructor 2; eauto.
Qed.

Lemma lem_is_var_app_shift : forall n m k t, is_var_app (n + k - m) t -> m <= n ->
                                             is_var_app (n + k) (shift m k t).
Proof.
  induction 1; intros; autorewrite with shints; try yelles 1.
  rewrite H; clear H; autorewrite with shints.
  ysplit.
  - assert (HH: n + k - m + m = n + k) by omega.
    ycrush.
  - bomega.
Qed.

Lemma lem_succ_shift : forall n m k t t', succ (n + k - m) t t' -> m <= n ->
                                          succ (n + k) (shift m k t) (shift m k t').
Proof.
  coinduction CH using eauto.
  - clear CH; pose lem_is_var_app_shift; ycrush.
  - intro H1.
    autorewrite with shints; simpl.
    apply succ_abs.
    assert (HH: n + k + 1 = n + (k + 1)) by omega.
    rewrite HH; clear HH.
    apply CH; clear CH; eauto.
    assert (n + k - m + 1 = n + (k + 1) - m) by omega.
    ycrush.
Qed.

Lemma lem_succ_subst :
  forall t t' s s' n, succ (n + 1) t t' -> forall m, m <= n -> succ (n - m) s s' ->
                                                     succ n (t [m := s]) (t' [m := s']).
Proof.
  coinduction CH using eauto.
  - clear CH; pose lem_is_var_app_subst; ycrush.
  - clear CH; intros.
    autorewrite with shints; repeat ysplit; try bomega.
    + apply succ_var.
    + assert (m0 = m) by bomega; subst.
      generalize (lem_succ_shift n m 0 s s'); intro HH; sauto; apply HH; try omega.
    + apply succ_var.
  - intros.
    autorewrite with shints.
    apply succ_abs.
    apply CH; clear CH; eauto.
    + omega.
    + assert (n + 1 - (m + 1) = n - m) by omega.
      ycrush.
Qed.

Definition step_beta_eq t s := step_beta t s \/ t == s.
Hint Unfold step_beta_eq.

Lemma lem_step_beta_preserves_succ :
  forall t t', step_beta t t' -> forall n s, succ n t s ->
                                             exists s', succ n t' s' /\ step_beta_eq s s'.
Proof.
  induction 1; intros n s Hs.
  - inversion_clear H.
    rewrite H0 in *; clear H0.
    inversion_clear Hs.
    + exists s; pose_term_eq; ycrush.
    + inversion_clear H.
      * exists (app t' s').
        assert (is_var_app n (app t' s')) by ycrush.
        pose_term_eq; ycrush.
      * exists (t'0 [0 := s']).
        split.
        ** rewrite H1; apply lem_succ_subst; sauto; omega.
        ** pose lem_step_beta_redex; pose_term_eq; ycrush.
  - rewrite H0 in *; clear H0.
    inversion_clear Hs.
    + exists s; pose_term_eq; ycrush.
    + yforwarding.
      exists (app s'0 s').
      destruct H3.
      * split; [ ycrush | left; pose_term_eq; ycrush ].
      * split; [ ycrush | right; pose_term_eq; ycrush ].
  - rewrite H0 in *; clear H0.
    inversion_clear Hs.
    + exists s; pose_term_eq; ycrush.
    + yforwarding.
      exists (app t' s'0).
      destruct H3.
      * split; [ ycrush | left; pose_term_eq; ycrush ].
      * split; [ ycrush | right; pose_term_eq; ycrush ].
  - inversion_clear Hs.
    + exists s; pose_term_eq; ycrush.
    + yforwarding.
      exists (abs s').
      destruct H2.
      * split; [ ycrush | left; pose_term_eq; ycrush ].
      * split; [ ycrush | right; pose_term_eq; ycrush ].
Qed.

Lemma lem_red_beta_preserves_succ :
  forall t t', red_beta t t' -> forall n s, succ n t s ->
                                            exists s', succ n t' s' /\ red_beta s s'.
Proof.
  induction 1.
  - pose_red_beta; ycrush.
  - intros.
    pose proof lem_step_beta_preserves_succ.
    yforwarding; yforwarding.
    exists s'1.
    split; eauto.
    destruct H4; pose_red_beta; ycrush.
Qed.

Lemma lem_step_beta_preserves_is_var_app :
  forall n t t', step_beta t t' -> is_var_app n t -> is_var_app n t'.
Proof.
  induction 1.
  - inversion_clear H; rewrite H0; intro HH; inversion_clear HH; yelles 2.
  - rewrite H0; intro HH; inversion_clear HH; yelles 2.
  - rewrite H0; intro HH; inversion_clear HH; yelles 2.
  - intro HH; inversion_clear HH; yelles 2.
Qed.

Lemma lem_step_beta_preserves_succ_2 :
  forall s s', step_beta s s' -> forall n t, succ n t s ->
                                             exists t', succ n t' s' /\ step_beta_eq t t'.
Proof.
  induction 1; intros n t Ht.
  - inversion_clear H.
    rewrite H0 in *; clear H0.
    inversion_clear Ht.
    + exfalso; iauto 3.
    + inversion_clear H.
      * exfalso; iauto 3.
      * exists (t3 [0 := s]).
        split.
        ** rewrite H1; apply lem_succ_subst; sauto; omega.
        ** pose lem_step_beta_redex; pose_term_eq; ycrush.
  - rewrite H0 in *; clear H0.
    inversion_clear Ht.
    + exists t.
      split.
      * pose lem_step_beta_preserves_is_var_app; constructor; ycrush.
      * pose_term_eq; ycrush.
    + yforwarding.
      exists (app t' s).
      destruct H3.
      * split; [ ycrush | left; pose_term_eq; ycrush ].
      * split; [ ycrush | right; pose_term_eq; ycrush ].
  - rewrite H0 in *; clear H0.
    inversion_clear Ht.
    + exists t.
      split.
      * pose lem_step_beta_preserves_is_var_app; constructor; ycrush.
      * pose_term_eq; ycrush.
    + yforwarding.
      exists (app t0 t').
      destruct H3.
      * split; [ ycrush | left; pose_term_eq; ycrush ].
      * split; [ ycrush | right; pose_term_eq; ycrush ].
  - inversion_clear Ht.
    + exfalso; iauto 3.
    + yforwarding.
      exists (abs t').
      destruct H2.
      * split; [ ycrush | left; pose_term_eq; ycrush ].
      * split; [ ycrush | right; pose_term_eq; ycrush ].
Qed.

Lemma lem_red_beta_preserves_succ_2 :
  forall s s', red_beta s s' -> forall n t, succ n t s ->
                                            exists t', succ n t' s' /\ red_beta t t'.
Proof.
  induction 1.
  - pose_red_beta; ycrush.
  - intros.
    pose proof lem_step_beta_preserves_succ_2.
    yforwarding; yforwarding.
    exists t'1.
    split; eauto.
    destruct H4; pose_red_beta; ycrush.
Qed.

Lemma lem_hlp_1 : forall n t t' s, inf_beta t t' -> is_abs t' -> is_var_app n (app t s) -> False.
Proof.
  unfold is_abs.
  intros; sauto.
  clear H4 t'.
  revert t x H2 s H1.
  enough (forall t y, red_beta t y -> forall x s, y = abs x -> is_var_app n (app t s) -> False) by scrush.
  induction 1.
  - intros; rewrite H in *; iauto 3.
  - pose lem_step_beta_preserves_is_var_app; yelles 3.
Qed.

Lemma lem_succ_preserves_rnf : forall n t t', succ n t t' -> is_rnf t -> is_rnf t'.
Proof.
  unfold is_rnf; sauto; eauto using lem_hlp_1.
  inversion_clear H.
  - eauto using lem_hlp_1.
  - unfold is_abs in H2; sauto.
    generalize (lem_red_beta_preserves_succ_2 t'1 (abs x) H2 n t1 H3).
    sauto.
    inversion H.
    + iauto 3.
    + pose_inf_beta; ycrush.
Qed.

Lemma lem_subst_succ : forall n t s, succ n (t [n := s]) (t [n := var 0]).
Proof.
  coinduction on 1.
  - intro; autorewrite with shints; repeat ysplit; pose_term_eq; csolve.
Qed.

Lemma lem_has_rnf_subst : forall n t1 t2, has_rnf (t1 [n := t2]) -> has_rnf t1.
Proof.
  unfold has_rnf.
  sauto.
  assert (exists s', is_rnf s' /\ red_beta (t1 [n := t2]) s') by
      Reconstr.reasy (@weak.lem_rnf_red_wh, @weak.lem_red_wh_to_red_beta) Reconstr.Empty.
  sauto.
  assert (succ n (t1 [n := t2]) (t1 [n := var 0])) by eauto using lem_subst_succ.
  assert (exists s1, red_beta (t1 [n := var 0]) s1 /\ succ n s' s1) by
      Reconstr.rblast (@lem_red_beta_preserves_succ) Reconstr.Empty.
  sauto.
  assert (is_rnf s1) by
      Reconstr.reasy (@lem_succ_preserves_rnf) (@defs.is_rnf).
  admit.
Admitted.
