Require Export weak.
Require Import cases.

Inductive step_wh_n : nat -> term -> term -> Prop :=
| step_wh_0 : forall t s, t == s -> step_wh_n 0 t s
| step_wh_more : forall n t s s', step_wh t s -> step_wh_n n s s' -> step_wh_n (S n) t s'.

Lemma lem_step_wh_n_morphism : forall n, morphism (step_wh_n n).
Proof.
  unfold morphism.
  induction 1.
  - pose_term_eq; ycrush.
  - intros; econstructor.
    + rewrite H1 in H; apply H.
    + pose_term_eq; ycrush.
Qed.

Add Parametric Morphism (n : nat) : (step_wh_n n) with
    signature term_eq ==> term_eq ==> iff as step_wh_n_mor.
Proof.
  split; intro; eapply lem_step_wh_n_morphism; pose_term_eq; eauto.
Qed.

Lemma lem_step_wh_n_to_red_wh : forall n t s, step_wh_n n t s -> red_wh t s.
Proof.
  induction 1; ycrush.
Qed.

Lemma lem_red_wh_to_step_wh_n : forall t s, red_wh t s -> exists n, step_wh_n n t s.
Proof.
  induction 1; ycrush.
Qed.

Lemma lem_step_wh_n_unique : forall n t s s', step_wh_n n t s -> step_wh_n n t s' -> s == s'.
Proof.
  induction n.
  - pose_term_eq; iauto 2.
  - intros t s s' H1 H2.
    inversion_clear H1.
    inversion_clear H2.
    pose lem_step_wh_unique; ycrush.
Qed.

Lemma lem_step_wh_n_decompose :
  forall m n t s s', step_wh_n n t s -> step_wh_n m t s' -> m >= n -> red_wh s s'.
Proof.
  induction m.
  - scrush.
  - intros.
    inversion_clear H0.
    assert (HH: (m = n - 1 /\ n > 0) \/ m >= n) by omega.
    destruct HH.
    + assert (m >= n - 1) by omega.
      assert (step_wh_n (n - 1) s0 s).
      inversion H; subst; sauto.
      assert (HH1: s1 == s0) by
	  Reconstr.reasy (@weak.lem_step_wh_unique) Reconstr.Empty.
      rewrite HH1 in *; scrush.
      ycrush.
    + destruct n.
      * assert (HH: t == s) by scrush.
        rewrite HH in *; clear HH.
        assert (red_wh s0 s') by
	    Reconstr.reasy (@lem_step_wh_n_to_red_wh) Reconstr.Empty.
        ycrush.
      * assert (m >= n) by omega.
        inversion_clear H.
        assert (HH: s1 == s0) by
	    Reconstr.reasy (@weak.lem_step_wh_unique) Reconstr.Empty.
        rewrite HH in *; clear HH.
        assert (red_wh s0 s') by
	    Reconstr.reasy (@lem_step_wh_n_to_red_wh) Reconstr.Empty.
        ycrush.
Qed.

Definition is_crnf t r := is_rnf r /\
                          exists n, step_wh_n n t r /\
                                    forall s m, step_wh_n m t s -> is_rnf s -> m >= n.
Hint Unfold is_crnf.

Lemma lem_crnf_exists : forall t, has_rnf t -> exists r, is_crnf t r.
Proof.
  intros t H.
  unfold has_rnf in H.
  destruct H as [t' [H1 H2]].
  generalize (lem_rnf_red_wh t t' H2 H1); intro HH; destruct HH as [s [HH1 [HH2 HH3]]].
  clear H2; revert HH1.
  rename HH2 into H.
  induction H; intros.
  - exists x; unfold is_crnf; split.
    + ycrush.
    + exists 0; split.
      * pose_term_eq; ycrush.
      * intros; omega.
  - generalize (is_rnf_xm x); intro Hd; destruct Hd as [ Hd | Hd ].
    + exists x; unfold is_crnf; split; [ auto | exists 0 ].
      split; [ pose_term_eq; ycrush | intros; omega ].
    + unfold is_crnf in *.
      generalize (IHstar HH3 HH1); intro HH; destruct HH as [r [Hr1 Hr2]].
      exists r; split; eauto; intros.
      destruct Hr2 as [n0 [Hr21 Hr22]].
      exists (S n0).
      split; [ econstructor; eauto | idtac ].
      intros.
      destruct H2.
      * rewrite H2 in *; ycrush.
      * assert (HH: s == y) by
	    Reconstr.reasy (@weak.lem_step_wh_unique) Reconstr.Empty.
        rewrite HH in *; clear HH.
        assert (n >= n0).
        apply Hr22 with (s := s'); eauto.
        omega.
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

Lemma lem_is_crnf_unique : forall t r r', is_crnf t r -> is_crnf t r' -> r == r'.
Proof.
  unfold is_crnf; sauto.
  assert (n >= n0) by scrush.
  assert (n0 >= n) by scrush.
  assert (n0 = n) by omega.
  pose lem_step_wh_n_unique; ycrush.
Qed.

Lemma lem_crnf_unique : forall t p p', crnf t p == crnf t p'.
Proof.
  pose lem_crnf_is_crnf; pose lem_is_crnf_unique; ycrush.
Qed.

Lemma lem_crnf_property :
  forall t r, is_crnf t r -> forall s, inf_beta t s -> is_rnf s -> red_wh t r /\ inf_wh r s.
Proof.
  intros.
  assert (exists s', is_rnf s' /\ red_wh t s' /\ inf_wh s' s) by
      Reconstr.reasy (@weak.lem_rnf_red_wh) Reconstr.Empty.
  unfold is_crnf in *; simp_hyps.
  assert (exists m, step_wh_n m t s') by
      Reconstr.reasy (@lem_red_wh_to_step_wh_n) Reconstr.Empty.
  simp_hyps.
  assert (m >= n) by scrush.
  assert (red_wh r s') by
      Reconstr.reasy (@lem_step_wh_n_decompose) Reconstr.Empty.
  Reconstr.reasy (@weak.lem_red_wh_refl, @weak.lem_beta_redex_to_step_wh, @lem_step_wh_n_to_red_wh, @weak.lem_aux_wh_to_inf_wh, @weak.lem_step_beta_to_inf_wh, @weak.lem_step_wh_to_inf_wh, @weak.lem_red_wh_to_inf_wh, @weak.lem_inf_beta_to_inf_wh, @weak.lem_red_beta_to_inf_wh, @weak.lem_inf_wh_prepend, @weak.lem_step_wh_to_red_wh) Reconstr.Empty.
Qed.

Lemma lem_red_wh_to_crnf : forall t (p : has_rnf t), red_wh t (crnf t p).
Proof.
  pose lem_crnf_is_crnf; pose lem_step_wh_n_to_red_wh; ycrush.
Qed.

Lemma lem_red_beta_to_crnf : forall t (p : has_rnf t), red_beta t (crnf t p).
Proof.
  Reconstr.reasy (lem_red_wh_to_crnf, lem_red_wh_to_red_beta) Reconstr.Empty.
Qed.

Lemma lem_crnf_not_bot : forall t p, crnf t p <> bot.
Proof.
  intros.
  generalize (lem_crnf_is_crnf t p).
  intro H.
  destruct H.
  destruct (crnf t p); sauto.
Qed.

Lemma lem_is_crnf_morphism : forall t t' r, t == t' -> is_crnf t r -> is_crnf t' r.
Proof.
  unfold is_crnf.
  sauto.
  exists n.
  sauto.
  - rewrite <- H; auto.
  - rewrite <- H in *; eauto.
Qed.

Lemma lem_crnf_morphism : forall t t' p p', t == t' -> crnf t p == crnf t' p'.
Proof.
  intros.
  assert (is_crnf t (crnf t p)) by (pose lem_crnf_is_crnf; ycrush).
  assert (is_crnf t' (crnf t' p')) by (pose lem_crnf_is_crnf; ycrush).
  assert (is_crnf t' (crnf t p)) by (pose lem_is_crnf_morphism; ycrush).
  pose lem_is_crnf_unique; ycrush.
Qed.
