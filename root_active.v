
Require Import weak.
Require Import sim.
Require Import cases.

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

Lemma lem_subst0_step : forall t s, step_beta t s ->
                                    forall n t0, t == t0 [n := var 0] ->
                                                 exists s0, s == s0 [n := var 0] /\ step_beta t0 s0.
Proof.
  induction 1.
  - inversion_clear H; intros.
    rewrite H in *; clear H.
    inversion H0; subst; yisolve; fold term_eq in *.
    destruct t0; autorewrite with shints in *; sauto.
    destruct t0_1; autorewrite with shints in *; try yelles 1.
    inversion H4; yisolve; fold term_eq in *.
    exists (t0_1 [0 := t0_2]).
    split.
    + generalize (lem_subst_eq n 0 (var 0) t0_1 t0_2); autorewrite with yhints; intro HH.
      rewrite HH.
      rewrite H3.
      rewrite H5.
      assumption.
    + Reconstr.reasy (lem_step_beta_redex) Reconstr.Empty.
  - intros.
    inversion H1; subst; yisolve; fold term_eq in *.
    destruct t0; autorewrite with shints in *; sauto.
    generalize (IHcomp_clos n t0_1 H5); intro HH; destruct HH as [s0 [HH1 HH2]].
    exists (app s0 t0_2).
    rewrite <- H0.
    rewrite HH1.
    autorewrite with shints.
    pose_term_eq; ycrush.
  - intros.
    inversion H1; subst; yisolve; fold term_eq in *.
    destruct t0; autorewrite with shints in *; sauto.
    generalize (IHcomp_clos n t0_2 H6); intro HH; destruct HH as [s0 [HH1 HH2]].
    exists (app t0_1 s0).
    rewrite <- H0.
    rewrite HH1.
    autorewrite with shints.
    pose_term_eq; ycrush.
  - intros.
    destruct t0; autorewrite with shints in *; sauto.
    inversion H0; subst; yisolve; fold term_eq in *.
    generalize (IHcomp_clos (n + 1) t0 H3); intro HH; destruct HH as [s0 [HH1 HH2]].
    exists (abs s0).
    rewrite HH1.
    autorewrite with shints.
    pose_term_eq; ycrush.
Qed.

Lemma lem_subst0_red : forall t s, red_beta t s ->
                                   forall n t0, t == t0 [n := var 0] ->
                                                exists s0, s == s0 [n := var 0] /\ red_beta t0 s0.
Proof.
  induction 1; pose_red_beta; pose_term_eq; pose lem_subst0_step; ycrush.
Qed.

Lemma lem_subst0_rnf : forall t, is_rnf t -> forall n t0, t == t0 [n := var 0] -> is_rnf t0.
Proof.
  destruct t; sauto; destruct t0; autorewrite with shints in *; sauto.
  destruct z; sauto.
  inversion_clear H0; yisolve; fold term_eq in *.
  assert (red_beta t1 ((abs x) [n := var 0])) by (pose lem_red_beta_subst_closed; ycrush).
  autorewrite with shints in *.
  pose_inf_beta; ycrush.
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
  assert (exists s0, s1 == s0 [n := var 0] /\ red_beta t1 s0) by
      (pose lem_subst0_red; pose_term_eq; ycrush).
  sauto.
  assert (is_rnf s0) by
      Reconstr.reasy (@lem_subst0_rnf) (@defs.is_rnf).
  Reconstr.reasy (lem_red_beta_to_inf_beta) Reconstr.Empty.
Qed.

Lemma lem_is_rnf_shift : forall d c t, is_rnf (shift d c t) -> is_rnf t.
Proof.
  unfold is_rnf; sauto.
  generalize lem_inf_beta_shift_closed; unfold shift_closed; ycrush.
Qed.

Lemma lem_has_rnf_shift : forall d c t, has_rnf (shift d c t) -> has_rnf t.
Proof.
  unfold has_rnf.
  sauto.
  assert (exists s, is_rnf s /\ red_beta (shift d c t) s) by
      Reconstr.reasy (@weak.lem_rnf_red_wh, @weak.lem_red_wh_to_red_beta) Reconstr.Empty.
  sauto.
  assert (exists s', s == shift d c s' /\ red_beta t s') by
      (pose lem_red_beta_shift; pose_term_eq; ycrush).
  sauto.
  exists s'.
  split.
  - rewrite H3 in H1; pose lem_is_rnf_shift; ycrush.
  - pose_inf_beta; ycrush.
Qed.

Lemma lem_ra_subst : forall n t1 t2, root_active t1 -> root_active (t1 [n := t2]).
Proof.
  Reconstr.reasy (@lem_has_rnf_subst) (root_active).
Qed.

Lemma lem_ra_shift : forall d c t, root_active t -> root_active (shift d c t).
Proof.
  Reconstr.reasy (@lem_has_rnf_shift) (@defs.root_active).
Qed.

Definition sim_ra := sim root_active.
Hint Unfold sim_ra.

Lemma lem_sim_ra_shift : forall n m t t', sim_ra t t' ->
                                          sim_ra (shift n m t) (shift n m t').
Proof.
  pose lem_ra_shift; coinduction.
Qed.

Lemma lem_sim_ra_subst : forall n t t' s s', sim_ra t t' -> sim_ra s s' ->
                                             sim_ra (t [n := s]) (t' [n := s']).
Proof.
  pose lem_ra_subst; pose lem_sim_ra_shift; coinduction.
Qed.

Lemma lem_inf_beta_preserves_ra : forall t s, inf_beta t s -> root_active t -> root_active s.
Proof.
  unfold root_active; unfold has_rnf; pose_inf_beta; ycrush.
Qed.

Lemma lem_ra_morphism : forall t s, t == s -> root_active t -> root_active s.
Proof.
  unfold root_active; unfold has_rnf; pose_term_eq; ycrush.
Qed.

Lemma lem_sim_ra_morphism : morphism sim_ra.
Proof.
  unfold morphism.
  coinduction CH.
  - clear CH; pose lem_ra_morphism; pose_term_eq; ycrush.
  - intros.
    destruct x'0, y'0; try solve [ clear CH; yelles 1 ].
    inversion_clear H2; yisolve.
    inversion_clear H3; yisolve.
    fold term_eq in *.
    constructor 4.
    eapply CH with (x := x0) (y := x'); clear CH; pose_term_eq; ycrush.
    eapply CH with (x := y0) (y := y'); clear CH; pose_term_eq; ycrush.
Qed.

Add Parametric Morphism : sim_ra  with
    signature term_eq ==> term_eq ==> iff as sim_ra_mor.
Proof.
  pose lem_sim_ra_morphism; pose_term_eq; ycrush.
Qed.

Lemma lem_ra_not_abs : forall x, ~(root_active (abs x)).
Proof.
  unfold root_active, not, has_rnf; pose_inf_beta; ycrush.
Qed.

Lemma lem_ra_not_var : forall n, ~(root_active (var n)).
Proof.
  unfold root_active, not, has_rnf; pose_inf_beta; ycrush.
Qed.

Lemma lem_step_beta_preserves_sim_ra :
  forall t t', step_beta t t' -> forall s, sim_ra t s -> exists s', step_beta_eq s s' /\ sim_ra t' s'.
Proof.
  induction 1.
  - intros s HH.
    inversion HH; subst.
    + exists s.
      assert (inf_beta x y) by
          Reconstr.rcrush (lem_step_beta_to_inf_beta, @defs.wh_base) Reconstr.Empty.
      pose lem_inf_beta_preserves_ra; pose_term_eq; ycrush.
    + sauto.
    + sauto.
    + inversion_clear H.
      inversion H2; subst; yisolve; fold term_eq in *.
      destruct x0; sauto.
      inversion H6; subst; yisolve; fold term_eq in *.
      inversion H0; subst; yisolve; fold term_eq in *.
      * pose lem_ra_not_abs; ycrush.
      * rewrite H8 in *.
        rewrite H5 in *.
        assert (sim_ra (t1 [0 := t2]) (y1 [0 := y'])) by
            (pose lem_sim_ra_subst; ycrush).
        exists (y1 [0 := y']).
        rewrite H3.
        Reconstr.reasy (@beta.lem_step_beta_redex) (@step_beta_eq).
    + scrush.
  - intros s HH.
    rewrite H0 in *; clear H0 y.
    inversion HH; subst.
    + exists s.
      assert (inf_beta (app x y') (app x' y')) by
          Reconstr.reasy (@beta.lem_step_beta_to_red_beta, @beta.lem_red_beta_to_inf_beta, @beta.lem_inf_beta_app, @equality.lem_term_eq_refl, @beta.lem_red_beta_refl) (@defs.term_eq, @defs.step_beta, @Coq.Relations.Relation_Definitions.reflexive).
      pose lem_inf_beta_preserves_ra; pose_term_eq; ycrush.
    + generalize (IHcomp_clos x'0 H2); sauto.
      exists (app s' y'0).
      unfold step_beta_eq in *; pose_term_eq; ycrush.
  - intros s HH.
    rewrite H0 in *; clear H0 x.
    inversion HH; subst.
    + exists s.
      assert (inf_beta (app x' y) (app x' y')) by
          Reconstr.reasy (@beta.lem_step_beta_to_red_beta, @beta.lem_red_beta_to_inf_beta, @beta.lem_inf_beta_app, @equality.lem_term_eq_refl, @beta.lem_red_beta_refl) (@defs.term_eq, @defs.step_beta, @Coq.Relations.Relation_Definitions.reflexive).
      pose lem_inf_beta_preserves_ra; pose_term_eq; ycrush.
    + generalize (IHcomp_clos y'0 H4); sauto.
      exists (app x'0 s').
      unfold step_beta_eq in *; pose_term_eq; ycrush.
  - intros s HH.
    inversion HH; subst.
    + Reconstr.reasy (@lem_ra_not_abs) Reconstr.Empty.
    + generalize (IHcomp_clos y0 H1); sauto.
      exists (abs s').
      unfold step_beta_eq in *; pose_term_eq; ycrush.
Qed.

Lemma lem_red_beta_preserves_sim_ra :
  forall t t', red_beta t t' -> forall s, sim_ra t s -> exists s', red_beta s s' /\ sim_ra t' s'.
Proof.
  induction 1.
  - intros; rewrite H in *; unfold step_beta_eq; pose_term_eq; ycrush.
  - intros.
    generalize (lem_step_beta_preserves_sim_ra x y H s H1); sauto.
    generalize (IHstar s' H3); sauto.
    destruct H2; pose_red_beta; pose_term_eq; ycrush.
Qed.

Lemma lem_sim_ra_preserves_rnf : forall t s, sim_ra t s -> is_rnf t -> is_rnf s.
Proof.
  intros.
  assert (~(root_active t)) by
      Reconstr.reasy (@weak.lem_inf_wh_to_inf_beta, @weak.lem_inf_wh_refl_0) (@defs.inf_wh, @defs.has_rnf, @defs.root_active, @Coq.Relations.Relation_Definitions.reflexive).
  destruct t; sauto.
  - pose lem_ra_not_var; scrush.
  - inversion H; sauto.
    destruct z; sauto.
    assert (HH: sim_ra x' t1) by (pose_sim; ycrush).
    generalize (lem_red_beta_preserves_sim_ra x' (abs x) H5 t1 HH); sauto.
    apply H0 with (z := s').
    + pose_inf_beta; ycrush.
    + destruct s'; pose lem_ra_not_abs; sauto.
  - inversion H; sauto.
Qed.

Lemma lem_sim_ra_preserves_ra : forall t s, sim_ra t s -> root_active t -> root_active s.
Proof.
  unfold root_active, not, has_rnf.
  sauto.
  apply H0; clear H0.
  assert (exists s', is_rnf s' /\ red_beta s s') by
      Reconstr.reasy (@weak.lem_rnf_red_wh, @weak.lem_red_wh_to_red_beta) Reconstr.Empty.
  sauto.
  assert (sim_ra s t) by (pose_sim; ycrush).
  assert (exists t0, red_beta t t0 /\ sim_ra s' t0) by
      (pose lem_red_beta_preserves_sim_ra; ycrush).
  pose_inf_beta; pose lem_sim_ra_preserves_rnf; ycrush.
Qed.

Lemma lem_ra_expansion : forall t s, inf_beta t s -> root_active s -> root_active t.
Proof.
  unfold root_active, not, has_rnf.
  sauto.
  apply H0; clear H0.
  assert (exists t0, is_rnf t0 /\ red_wh t t0) by
      Reconstr.reasy (@weak.lem_rnf_red_wh) Reconstr.Empty.
  sauto.
  assert (exists r, red_wh s r /\ inf_beta t0 r) by
      Reconstr.rblast (@weak.lem_rnf_red_wh, @beta.lem_inf_beta_prepend, @weak.lem_inf_wh_to_inf_beta, @weak.lem_wh_commute, @weak.lem_inf_beta_to_inf_wh) (@defs.has_rnf).
  sauto.
  assert (is_rnf r) by
      Reconstr.reasy (@beta.lem_inf_beta_preserves_rnf) Reconstr.Empty.
  exists r.
  Reconstr.reasy (@beta.lem_red_beta_to_inf_beta, @weak.lem_red_wh_to_inf_wh, @weak.lem_inf_wh_to_inf_beta) Reconstr.Empty.
Qed.

Theorem thm_ra_strongly_meaningless : strongly_meaningless root_active.
Proof.
  unfold strongly_meaningless, meaningless.
  repeat split.
  - unfold root_active, not, has_rnf.
    sauto.
    destruct t'; sauto.
    + assert (bot == var n) by (pose lem_red_beta_preserves_bot; pose_term_eq; ycrush).
      scrush.
    + assert (bot == app x y) by (pose lem_red_beta_preserves_bot; pose_term_eq; ycrush).
      scrush.
    + assert (bot == abs x) by (pose lem_red_beta_preserves_bot; pose_term_eq; ycrush).
      scrush.
  - Reconstr.reasy (@lem_inf_beta_preserves_ra) Reconstr.Empty.
  - Reconstr.reasy (@lem_ra_subst) Reconstr.Empty.
  - Reconstr.reasy (@lem_ra_shift) Reconstr.Empty.
  - Reconstr.reasy (@lem_ra_not_abs) Reconstr.Empty.
  - auto.
  - Reconstr.reasy (@lem_sim_ra_preserves_ra) (@sim_ra, @defs.has_rnf, @defs.is_rnf, @defs.root_active).
  - Reconstr.reasy (@lem_ra_expansion) Reconstr.Empty.
Qed.
