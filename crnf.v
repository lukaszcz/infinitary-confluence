Require Export weak.
Require Import cases.

Lemma lem_wh_step_1 : forall t w u s, step_wh t w -> step_wh t u -> inf_wh u s ->
                                      exists x, step_wh_eq s x /\ inf_wh w x.
Proof.
  intros t w u s H1 H2 H3.
  exists s.
  assert (HH: w == u) by eauto using lem_step_wh_unique.
  rewrite HH; clear HH.
  pose_term_eq; ycrush.
Qed.

Lemma lem_wh_step_commute : forall t t1 t2, inf_wh t t1 -> step_wh t t2 ->
                                            exists t3, step_wh_eq t1 t3 /\ inf_wh t2 t3.
Proof.
  intros t t1 t2 H1 H2.
  revert t1 H1.
  induction H2; subst.
  - intros t1 H2.
    assert (step_wh x y) by ycrush.
    inversion_clear H; subst.
    inversion_clear H2; subst.
    + generalize (lem_red_wh_rev x _ H); sintuition.
      * eapply lem_wh_step_1; pose_inf_wh; ycrush.
      * rewrite H4 in *; exfalso; yelles 1.
    + generalize (lem_red_wh_rev x _ H); sintuition.
      * eapply lem_wh_step_1; pose_inf_wh; ycrush.
      * rewrite H4 in *; exfalso; yelles 1.
    + generalize (lem_red_wh_rev x _ H); sintuition.
      * eapply lem_wh_step_1; pose_inf_wh; ycrush.
      * rewrite H6 in *.
        inversion_clear H1; subst; sintuition; fold term_eq inf_wh in *.
        rewrite H2 in *; rewrite H7 in *.
        inversion_clear H4; subst; sintuition; fold term_eq inf_wh in *;
          try solve [ pose lem_red_wh_from_abs; yforwarding; yelles 1 ].
        assert (HH: x1 == t0) by (pose lem_red_wh_from_abs; ycrush).
        rewrite HH in *; clear HH.
        exists (x'0 [0 := y']).
        split.
        ** pose lem_step_wh_redex; ycrush.
        ** pose lem_inf_wh_subst; ycrush.
    + generalize (lem_red_wh_rev x _ H); sintuition.
      * eapply lem_wh_step_1; pose_inf_wh; ycrush.
      * rewrite H5 in *; exfalso; yelles 1.
  - intros t1 H1.
    rewrite H in *.
    assert (step_wh (app x y) (app x' y')) by (pose_term_eq; ycrush).
    inversion_clear H1; subst.
    + generalize (lem_red_wh_rev (app x y') _ H3); sintuition.
      * eapply lem_wh_step_1; rewrite H in *; pose_inf_wh; ycrush.
      * exfalso; yelles 1.
    + generalize (lem_red_wh_rev (app x y') _ H3); sintuition.
      * eapply lem_wh_step_1; rewrite H in *; pose_inf_wh; ycrush.
      * exfalso; yelles 1.
    + generalize (lem_red_wh_rev (app x y') _ H3); sintuition.
      * eapply lem_wh_step_1; rewrite H in *; pose_inf_wh; ycrush.
      * inversion_clear H6; subst; sintuition; fold term_eq inf_wh in *.
        rewrite <- H1 in *; rewrite <- H7 in *.
        generalize (IHstep_wh x'0 H4); sintuition.
        exists (app t3 y'0).
        split.
        ** destruct H6; [ left | right ]; pose_term_eq; ycrush.
        ** pose_inf_wh; ycrush.
    + generalize (lem_red_wh_rev (app x y') _ H3); sintuition.
      * eapply lem_wh_step_1; rewrite H in *; pose_inf_wh; ycrush.
      * exfalso; yelles 1.
Qed.

Lemma lem_wh_commute : forall t t1 t2, inf_wh t t1 -> red_wh t t2 ->
                                       exists t3, red_wh t1 t3 /\ inf_wh t2 t3.
Proof.
  intros t t1 t2 H1 H.
  revert t1 H1.
  induction H.
  - intros; rewrite H in *; pose_red_wh; ycrush.
  - intros t1 H1.
    generalize (lem_wh_step_commute x t1 y H1 H); sintuition.
    unfold step_wh_eq in *; pose_red_wh; ycrush.
Qed.

Lemma lem_rnf_red_wh : forall t s, inf_beta t s -> is_rnf s ->
                                   exists s', is_rnf s' /\ red_wh t s' /\ inf_wh s' s.
Proof.
  intros t s H1 H2.
  assert (H1w: inf_wh t s) by reasy (lem_inf_beta_to_inf_wh) Reconstr.Empty.
  unfold is_rnf in H2.
  destruct s.
  - yelles 1.
  - unfold is_rnf; exists (var n); pose_inf_wh; scrush.
  - inversion_clear H1w; subst; fold inf_wh in *.
    enough (is_rnf (app x y)) by (pose_inf_wh; scrush).
    unfold is_rnf, is_abs, not; intros z HH ?; destruct z; yisolve.
    assert (HH1: exists u, inf_wh x (abs u)) by reasy (lem_inf_beta_to_inf_wh) Reconstr.Empty.
    assert (HH2: exists u, red_wh x (abs u)) by (clear -HH1; scrush).
    clear HH1.
    destruct HH2 as [u].
    assert (HH3: exists r, inf_wh (abs u) r /\ red_wh s1 r) by
        (clear -H5 H0; pose lem_wh_commute; ycrush).
    destruct HH3 as [r [HH1 HH2]].
    assert (is_abs r) by (clear -HH1; pose lem_inf_wh_from_abs; ycrush).
    pose_inf_wh; pose lem_inf_wh_to_inf_beta; ycrush.
  - inversion H1w; unfold is_rnf; exists (abs x); pose_inf_wh; scrush.
Qed.

Definition is_crnf t r := is_rnf r /\ forall s, inf_beta t s -> is_rnf s -> red_wh t r /\ inf_wh r s.
Hint Unfold is_crnf.

Add Parametric Morphism : is_rnf with
    signature term_eq ==> iff as step_wh_mor.
Proof.
  split; unfold is_rnf; sauto; inversion H; ycrush.
Qed.

Lemma lem_crnf_exists : forall t, has_rnf t -> exists r, is_crnf t r.
Proof.
  intros t H.
  unfold has_rnf in H.
  destruct H as [t' [H1 H2]].
  generalize (lem_rnf_red_wh t t' H2 H1); intro HH; destruct HH as [s [HH1 [HH2 HH3]]].
  clear H2; revert HH1.
  rename HH2 into H.
  induction H; intros.
  - exists x; unfold is_crnf; split; intros; rewrite H in *; pose_red_wh; pose lem_inf_beta_to_inf_wh; ycrush.
  - generalize (is_rnf_dec x); intro Hd; destruct Hd as [ Hd | Hd ].
    + exists x; unfold is_crnf; pose_red_wh; pose lem_inf_beta_to_inf_wh; ycrush.
    + unfold is_crnf in *.
      generalize (IHstar HH3 HH1); intro HH; destruct HH as [r [Hr1 Hr2]].
      exists r; split; eauto; intros.
      generalize (lem_rnf_red_wh x s H2 H3); intro HH; destruct HH as [s' [H4 [H5 H6]]].
      inversion_clear H5; subst.
      * exfalso; rewrite H7 in *; ycrush.
      * assert (Hy0: y0 == y) by reasy (@weak.lem_step_wh_unique) Reconstr.Empty.
        rewrite Hy0 in *; clear Hy0.
        assert (red_wh y s') by ycrush.
        assert (inf_beta y s) by (pose_inf_wh; pose lem_inf_wh_to_inf_beta; ycrush).
        pose_red_wh; ycrush.
Qed.

Definition crnf0 t (p : has_rnf t) : { r | is_crnf t r }.
  apply constructive_indefinite_description.
  apply lem_crnf_exists.
  assumption.
Defined.

Definition crnf t (p : has_rnf t) := proj1_sig (crnf0 t p).

Lemma lem_crnf_is_crnf : forall t (p : has_rnf t), is_crnf t (crnf t p).
Proof.
  intros; unfold crnf.
  destruct (crnf0 t p); sauto.
Qed.
