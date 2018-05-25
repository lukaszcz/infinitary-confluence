Require Export weak.
Require Import cases.

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
