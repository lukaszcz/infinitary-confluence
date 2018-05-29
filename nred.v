
Require Import crnf.
Require Import botred.

Section RedNu.

Variable U : term -> Prop.
Variable Hm : meaningless U.
Variable U_dec : forall t, {U t}+{~(U t)}.

Lemma lem_not_U_has_rnf : forall t, ~(U t) -> has_rnf t.
Proof.
  intros.
  enough (~~(has_rnf t)) by (pose has_rnf_dec; ycrush).
  ycrush.
Qed.

CoInductive red_nu : term -> term -> Prop :=
| red_nu_var : forall t n (p : ~ U t), crnf t (lem_not_U_has_rnf t p) == (var n) -> red_nu t (var n)
| red_nu_app : forall t t1 t2 s1 s2 (p : ~ U t), crnf t (lem_not_U_has_rnf t p) == (app t1 t2) ->
                                                 red_nu t1 s1 -> red_nu t2 s2 -> red_nu t (app s1 s2)
| red_nu_abs : forall t t0 s (p : ~ U t), crnf t (lem_not_U_has_rnf t p) == (abs t0) ->
                                          red_nu t0 s -> red_nu t (abs s)
| red_nu_U : forall t, U t -> red_nu t bot.

Lemma lem_red_nu_morphism : morphism red_nu.
Proof.
  unfold morphism.
  coinduct CH; intros.
  - clear CH.
    assert (HH: ~ U x').
    destruct (U_dec x'); auto.
    assert (U x) by (pose lem_U_morphism; pose_term_eq; ycrush).
    exfalso; eauto.
    assert (crnf x' (lem_not_U_has_rnf x' HH) == var n).
    pose lem_crnf_morphism; pose_term_eq; ycrush.
    destruct y'; sauto.
    eapply red_nu_var; pose_term_eq; eauto.
  - assert (HH: ~ U x').
    clear CH; destruct (U_dec x'); auto.
    assert (U x) by (pose lem_U_morphism; pose_term_eq; ycrush).
    exfalso; eauto.
    assert (crnf x' (lem_not_U_has_rnf x' HH) == app t1 t2).
    clear CH; pose lem_crnf_morphism; pose_term_eq; ycrush.
    destruct y'; try solve [ clear CH; sauto ].
    inversion H4; subst; try solve [ exfalso; assumption ]; fold term_eq in *.
    eapply red_nu_app with (t1 := t1) (t2 := t2).
    * clear CH; eauto.
    * eapply CH with (x := t1) (y := s1); solve [ assumption | reflexivity ].
    * eapply CH with (x := t2) (y := s2); solve [ assumption | reflexivity ].
  - assert (HH: ~ U x').
    clear CH; destruct (U_dec x'); auto.
    assert (U x) by (pose lem_U_morphism; pose_term_eq; ycrush).
    exfalso; eauto.
    assert (crnf x' (lem_not_U_has_rnf x' HH) == abs t0).
    clear CH; pose lem_crnf_morphism; pose_term_eq; ycrush.
    destruct y'; try solve [ clear CH; sauto ].
    inversion H3; subst; try solve [ exfalso; assumption ]; fold term_eq in *.
    eapply red_nu_abs with (t0 := t0).
    * clear CH; eauto.
    * eapply CH with (x := t0) (y := s); solve [ assumption | reflexivity ].
  - clear CH.
    destruct y'; sauto.
    assert (U x') by (pose lem_U_morphism; pose_term_eq; ycrush).
    ycrush.
Qed.

Add Parametric Morphism : red_nu with
    signature term_eq ==> term_eq ==> iff as red_nu_mor.
Proof.
  split; intro; eapply lem_red_nu_morphism; pose_term_eq; eauto.
Qed.

Lemma lem_red_beta_bot_to_crnf : forall t (p : has_rnf t), red_beta_bot U t (crnf t p).
Proof.
  Reconstr.reasy (lem_red_wh_to_red_beta, lem_red_beta_to_red_beta_bot, lem_red_wh_to_crnf) Reconstr.Empty.
Qed.

Lemma lem_red_nu_to_red_beta_bot :
  forall t s, red_nu t s -> inf_beta_bot U t s.
Proof.
  pose lem_red_beta_bot_to_crnf; pose lem_red_beta_bot_morphism; pose lem_red_beta_bot_redex_U; pose_term_eq;
    coinduction.
Qed.

CoFixpoint F_red_nu_reduct (t : term) : term.
destruct (U_dec t) as [H | H].
- exact bot.
- destruct (crnf t (lem_not_U_has_rnf t H)) eqn:Ht.
  + exact bot.
  + exact (var n).
  + exact (app (F_red_nu_reduct t0_1) (F_red_nu_reduct t0_2)).
  + exact (abs (F_red_nu_reduct t0)).
Defined.

Lemma lem_red_nu_reduct : forall t, exists s, red_nu t s.
Proof.
  enough (exists f, forall t, red_nu t (f t)) by ycrush.
  exists F_red_nu_reduct.
  cofix CH.
  intro t.
  peek (F_red_nu_reduct t).
  destruct (U_dec t) as [H | H].
  - clear CH; constructor; assumption.
  - destruct (crnf t (lem_not_U_has_rnf t H)) eqn:Ht.
    + clear CH; pose lem_crnf_not_bot; ycrush.
    + clear CH; eapply red_nu_var; pose_term_eq; ycrush.
    + econstructor.
      * clear CH; pose_term_eq; ycrush.
      * eapply CH.
      * eapply CH.
    + econstructor.
      * clear CH; pose_term_eq; ycrush.
      * eapply CH.
Qed.

Lemma lem_red_nu_unique : forall t s1 s2, red_nu t s1 -> red_nu t s2 -> s1 == s2.
Proof.
  coinduction CH using eauto.
  - clear CH; intro HH2; destruct HH2.
    + pose lem_crnf_unique; pose_term_eq; eauto.
    + assert (var n == app t1 t2) by
          (pose lem_crnf_unique; pose_term_eq; eauto).
      exfalso; iauto 1.
    + assert (var n == abs t0) by
          (pose lem_crnf_unique; pose_term_eq; eauto).
      exfalso; iauto 1.
    + pose lem_crnf_unique; pose_term_eq; yelles 2.
  - intro HH2; destruct HH2.
    + clear CH.
      assert (HH: crnf t (lem_not_U_has_rnf t p) == crnf t (lem_not_U_has_rnf t p0)) by
          (pose lem_crnf_unique; pose_term_eq; eauto).
      rewrite HH in *; clear HH.
      assert (app t1 t2 == var n) by (pose_term_eq; eauto).
      exfalso; iauto 1.
    + assert (HH: crnf t (lem_not_U_has_rnf t p) == crnf t (lem_not_U_has_rnf t p0)) by
          (clear CH; pose lem_crnf_unique; pose_term_eq; eauto).
      assert (H4: app t1 t2 == app t0 t3) by
          (clear CH; pose_term_eq; eauto).
      inversion H4; [ exfalso; assumption | idtac ]; fold term_eq in *; subst.
      rewrite H8 in *.
      rewrite H10 in *.
      apply par_clos_app; fold term_eq; eapply CH; clear CH; eauto.
    + clear CH.
      assert (HH: crnf t (lem_not_U_has_rnf t p) == crnf t (lem_not_U_has_rnf t p0)) by
          (pose lem_crnf_unique; pose_term_eq; eauto).
      rewrite HH in *; clear HH.
      assert (app t1 t2 == abs t0) by (pose_term_eq; eauto).
      exfalso; iauto 1.
    + clear CH; yisolve.
  - intro HH2; destruct HH2.
    + clear CH.
      assert (HH: crnf t (lem_not_U_has_rnf t p) == crnf t (lem_not_U_has_rnf t p0)) by
          (pose lem_crnf_unique; pose_term_eq; eauto).
      rewrite HH in *; clear HH.
      assert (abs t1 == var n) by (pose_term_eq; eauto).
      exfalso; iauto 1.
    + assert (HH: crnf t (lem_not_U_has_rnf t p) == crnf t (lem_not_U_has_rnf t p0)) by
          (clear CH; pose lem_crnf_unique; pose_term_eq; eauto).
      assert (H4: abs t1 == app t0 t2) by
          (clear CH; pose_term_eq; eauto).
      clear CH; exfalso; iauto 1.
    + assert (HH: crnf t (lem_not_U_has_rnf t p) == crnf t (lem_not_U_has_rnf t p0)) by
          (clear CH; pose lem_crnf_unique; pose_term_eq; eauto).
      assert (H4: abs t1 == abs t0) by
          (clear CH; pose_term_eq; eauto).
      inversion H4; [ exfalso; assumption | idtac ]; fold term_eq in *; subst.
      rewrite H6 in *.
      apply par_clos_abs; fold term_eq; eapply CH; clear CH; eauto.
    + clear CH; yisolve.
Qed.

End RedNu.
