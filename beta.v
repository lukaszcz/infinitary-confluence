Require Export basics.

(************************************************************************************************)

Lemma lem_shift_0 : forall c t, shift 0 c t == t.
Proof.
  coinduction on 1 using ssolve.
Qed.

Lemma lem_shift_comp : forall m n k j t, shift m (k + j) (shift (n + k) j t) == shift (m + n + k) j t.
Proof.
  coinduction on 4.
  - clear H; autorewrite with shints; sauto; bnat_reflect; try omega.
    assert (n0 + m + n + k = n0 + n + k + m) by omega.
    scrush.
  - autorewrite with shints.
    constructor 5; fold term_eq.
    assert (k + j + 1 = k + (j + 1)) by omega.
    yelles 1.
Qed.

Lemma lem_shift_comp_0 : forall m n k t, shift m k (shift (n + k) 0 t) == shift (n + m + k) 0 t.
Proof.
  intros.
  assert (HH: n + m + k = m + n + k) by omega; rewrite HH; clear HH.
  generalize (lem_shift_comp m n k 0 t); autorewrite with yhints; intro HH.
  rewrite HH; reflexivity.
Qed.

Lemma lem_shift_plus : forall n m k s y, shift (n + m) k y == shift (n + m + 1) k y [m + k := s].
Proof.
  coinduction H on 4.
  - clear H; autorewrite with shints; sauto; bnat_reflect; try omega.
    assert (n1 = n0 + (n + m)) by omega.
    scrush.
  - autorewrite with shints.
    constructor 5; fold term_eq.
    assert (m + k + 1 = m + (k + 1)) by omega.
    yelles 1.
Qed.

Lemma lem_shift_plus_0 : forall n m s y, shift (n + m) 0 y == shift (n + m + 1) 0 y [m := s].
Proof.
  intros; rewrite lem_shift_plus; sauto.
Qed.

Lemma lem_shift_subst : forall n m k y s, shift m k s [n + m + k := y] == shift m k (s [n + k := y]).
Proof.
  coinduction H on 4.
  - clear H; autorewrite with shints; repeat ysplit; bnat_reflect; try omega.
    + autorewrite with shints; sauto; bomega.
    + rewrite lem_shift_comp_0; reflexivity.
    + autorewrite with shints; sauto; bomega.
    + autorewrite with shints; sauto; bomega.
  - autorewrite with shints.
    constructor 5; fold term_eq.
    assert (HH: n + m + k + 1 = n + m + (k + 1)) by omega; rewrite HH; clear HH.
    assert (HH: n + k + 1 = n + (k + 1)) by omega; rewrite HH; clear HH.
    auto.
Qed.

Lemma lem_shift_subst_0 : forall n m y s, shift m 0 s [n + m := y] == shift m 0 (s [n := y]).
Proof.
  intros.
  generalize (lem_shift_subst n m 0 y s); autorewrite with yhints; intro HH.
  rewrite HH; reflexivity.
Qed.

Lemma lem_subst_eq :
  forall n m y t s, t[m := s][n + m := y] == t[n+m+1 := y][m := s[n := y]].
Proof.
  coinduction H on 3; intros.
  - clear H.
    autorewrite with shints; repeat ysplit; try bomega;
      autorewrite with shints; repeat ysplit; try yelles 1; try bomega.
    + rewrite lem_shift_plus_0; sauto.
    + rewrite lem_shift_subst_0; sauto.
  - autorewrite with shints; sauto.
    constructor 5; fold term_eq.
    Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Arith.Plus.plus_assoc_reverse) Reconstr.Empty.
Qed.

Lemma lem_shift_comp_2 :
  forall d c n k t, shift d (c + n + k) (shift n k t) == shift n k (shift d (c + k) t).
Proof.
  coinduction H on 4.
  - clear H; autorewrite with shints; repeat ysplit; try yelles 1; try bomega.
    + assert (n0 + n + d = n0 + d + n) by omega.
      scrush.
  - autorewrite with shints.
    constructor 5; fold term_eq.
    assert (HH: forall m, m + k + 1 = m + (k + 1)) by (intros; omega).
    do 2 rewrite HH.
    auto.
Qed.

Lemma lem_shift_subst_2 :
  forall d c k t1 t2, shift d (c + k) (t1 [k := t2]) == shift d (c + k + 1) t1 [k := shift d c t2].
Proof.
  coinduction H on 3; intros.
  - clear H; autorewrite with shints; repeat ysplit; bnat_reflect; try omega.
    + autorewrite with shints; sauto; bomega.
    + autorewrite with shints; sauto; bomega.
    + generalize (lem_shift_comp_2 d c n 0 t2); autorewrite with yhints; auto.
    + autorewrite with shints; sauto; bomega.
  - autorewrite with shints.
    constructor 5; fold term_eq.
    assert (HH: c + k + 1 = c + (k + 1)) by omega.
    rewrite HH.
    auto.
Qed.

(************************************************************************************************)

Lemma lem_beta_redex_subst_closed : subst_closed beta_redex.
Proof.
  unfold subst_closed.
  intros x x' n y H.
  inversion H; subst.
  assert (x [n := y] == app (abs t1) t2 [n := y]) by (pose_term_eq; ycrush).
  assert (x' [n := y] == t1 [0 := t2] [n := y]) by (pose_term_eq; ycrush).
  autorewrite with shints in *.
  eapply beta_redex_c.
  - eauto.
  - generalize (lem_subst_eq n 0 y t1 t2); intro HH.
    autorewrite with yhints in *.
    rewrite <- HH; assumption.
Qed.

Lemma lem_beta_redex_shift_closed : shift_closed beta_redex.
Proof.
  unfold shift_closed.
  intros d c t t' H.
  inversion H as [ ? ? t1 t2 H1 H2 ]; subst.
  rewrite H1.
  rewrite H2.
  autorewrite with shints.
  eapply beta_redex_c.
  - pose_term_eq; eauto.
  - generalize (lem_shift_subst_2 d c 0 t1 t2); autorewrite with yhints; auto.
Qed.

(************************************************************************************************)

Lemma lem_step_beta_morphism : morphism step_beta.
Proof.
  unfold step_beta.
  apply lem_comp_morphism.
  apply lem_beta_redex_morphism.
Qed.

Lemma lem_red_beta_morphism : morphism red_beta.
Proof.
  unfold red_beta.
  apply lem_star_morphism.
  apply lem_step_beta_morphism.
Qed.

Lemma lem_inf_beta_morphism : morphism inf_beta.
Proof.
  unfold inf_beta.
  apply lem_inf_morphism.
  apply lem_step_beta_morphism.
Qed.

Add Parametric Morphism : step_beta with
    signature term_eq ==> term_eq ==> iff as step_beta_mor.
Proof.
  split; intro; eapply lem_step_beta_morphism; pose_term_eq; eauto.
Qed.

Add Parametric Morphism : red_beta with
    signature term_eq ==> term_eq ==> iff as red_beta_mor.
Proof.
  split; intro; eapply lem_red_beta_morphism; pose_term_eq; eauto.
Qed.

Add Parametric Morphism : inf_beta with
    signature term_eq ==> term_eq ==> iff as inf_beta_mor.
Proof.
  split; intro; eapply lem_inf_beta_morphism; pose_term_eq; eauto.
Qed.

Add Parametric Morphism : is_rnf with
    signature term_eq ==> iff as is_rnf_mor.
Proof.
  split; unfold is_rnf; sauto; inversion H; ycrush.
Qed.

(************************************************************************************************)

Lemma lem_step_beta_redex : forall x y, step_beta (app (abs x) y) (x [0 := y]).
Proof.
  constructor; econstructor; pose_term_eq; eauto.
Qed.

Lemma lem_red_beta_refl : forall x y, x == y -> red_beta x y.
Proof.
  apply lem_red_refl; apply lem_beta_redex_morphism.
Qed.

Lemma lem_red_beta_refl_0 : reflexive term red_beta.
Proof.
  apply lem_red_refl_0; apply lem_beta_redex_morphism.
Qed.

Lemma lem_red_beta_trans : transitive term red_beta.
Proof.
  apply lem_red_trans; apply lem_beta_redex_morphism.
Qed.

Lemma lem_red_beta_step : forall x y z, step_beta x y -> red_beta y z -> red_beta x z.
Proof.
  apply lem_red_step; apply lem_beta_redex_morphism.
Qed.

Lemma lem_red_beta_app : forall x x' y y', red_beta x x' -> red_beta y y' -> red_beta (app x y) (app x' y').
Proof.
  apply lem_red_app; apply lem_beta_redex_morphism.
Qed.

Lemma lem_red_beta_abs : forall x x', red_beta x x' -> red_beta (abs x) (abs x').
Proof.
  apply lem_red_abs; apply lem_beta_redex_morphism.
Qed.

Lemma lem_red_beta_step_rev : forall x y z, red_beta x y -> step_beta y z -> red_beta x z.
Proof.
  apply lem_red_step_rev; apply lem_beta_redex_morphism.
Qed.

Lemma lem_red_beta_redex : forall x y, red_beta (app (abs x) y) (x [0 := y]).
Proof.
  intros; econstructor 2.
  - eauto using lem_step_beta_redex.
  - constructor; pose_term_eq; eauto.
Qed.

Lemma lem_step_beta_to_red_beta : forall x y, step_beta x y -> red_beta x y.
Proof.
  apply lem_step_to_red; apply lem_beta_redex_morphism.
Qed.

Ltac pose_red_beta := pose proof lem_red_beta_refl_0; pose proof lem_red_beta_refl; pose proof lem_red_beta_trans;
                      pose proof lem_red_beta_step; pose proof lem_red_beta_step_rev;
                      pose proof lem_red_beta_redex; pose proof lem_step_beta_to_red_beta;
                      pose proof lem_red_beta_app; pose proof lem_red_beta_abs;
                      autounfold with shints in *.

(******************************************************************************)

Lemma lem_step_beta_shift_closed : shift_closed step_beta.
Proof.
  unfold step_beta.
  pose lem_beta_redex_morphism; pose lem_comp_shift_closed; pose lem_beta_redex_shift_closed; scrush.
Qed.

Lemma lem_red_beta_shift_closed : shift_closed red_beta.
Proof.
  unfold red_beta.
  pose lem_step_beta_morphism; pose lem_star_shift_closed; pose lem_step_beta_shift_closed; scrush.
Qed.

Lemma lem_inf_beta_shift_closed : shift_closed inf_beta.
Proof.
  pose lem_inf_shift_closed; pose lem_red_beta_shift_closed; scrush.
Qed.

Lemma lem_step_beta_subst_closed : subst_closed step_beta.
Proof.
  unfold step_beta.
  pose lem_beta_redex_morphism; pose lem_comp_subst_closed; pose lem_beta_redex_subst_closed; scrush.
Qed.

Lemma lem_red_beta_subst_closed : subst_closed red_beta.
Proof.
  unfold red_beta.
  pose lem_step_beta_morphism; pose lem_star_subst_closed; pose lem_step_beta_subst_closed; scrush.
Qed.

Lemma lem_inf_beta_subst :
  forall s s' t t', inf_beta s s' -> inf_beta t t' ->
                    forall n, inf_beta (subst n t s) (subst n t' s').
Proof.
  unfold inf_beta; unfold red_beta.
  pose lem_step_beta_subst_closed; pose lem_step_beta_shift_closed; apply lem_inf_subst; auto.
  apply lem_step_beta_morphism.
Qed.

Lemma lem_inf_beta_refl : reflexive term inf_beta.
Proof.
  unfold inf_beta; unfold red_beta; pose lem_inf_refl_0; scrush.
Qed.

Lemma lem_inf_beta_subst_closed : subst_closed inf_beta.
Proof.
  unfold subst_closed.
  pose lem_inf_beta_subst; pose lem_inf_beta_refl; scrush.
Qed.

Lemma lem_inf_beta_prepend : forall x y z, red_beta x y -> inf_beta y z -> inf_beta x z.
Proof.
  unfold inf_beta; unfold red_beta.
  pose lem_step_beta_morphism; pose lem_inf_prepend; eauto.
Qed.

Lemma lem_inf_beta_append_step : forall t1 t2 t3, inf_beta t1 t2 -> step_beta t2 t3 -> inf_beta t1 t3.
Proof.
  intros t1 t2 t3 H0 H.
  revert t1 H0.
  induction H; intros t1 HH.
  - inversion H; subst.
    rewrite H0 in HH.
    rewrite H1.
    inversion HH; subst; fold inf_beta in *.
    inversion H6; subst; fold inf_beta in *.
    assert (red_beta t1 (x1 [0 := y0])) by
        (pose_red_beta; eauto).
    eauto using lem_inf_beta_subst, lem_inf_beta_prepend.
  - rewrite H0 in HH; inversion HH; subst; fold inf_beta in *.
    econstructor; fold inf_beta; eauto.
  - rewrite H0 in HH; inversion HH; subst; fold inf_beta in *.
    econstructor; fold inf_beta; eauto.
  - inversion HH; subst; fold inf_beta in *.
    econstructor; fold inf_beta; eauto.
Qed.

Lemma lem_inf_beta_append : forall t1 t2 t3, inf_beta t1 t2 -> red_beta t2 t3 -> inf_beta t1 t3.
Proof.
  intros t1 t2 t3 H1 H2.
  revert t1 H1.
  induction H2; intros.
  - rewrite <- H; assumption.
  - pose lem_inf_beta_append_step; eauto.
Qed.

Lemma lem_inf_beta_appendable : appendable red_beta.
Proof.
  unfold appendable; pose lem_inf_beta_append; eauto.
Qed.

Lemma lem_inf_beta_trans : transitive term inf_beta.
Proof.
  eauto using lem_inf_trans, lem_inf_beta_appendable.
Qed.

Lemma lem_red_beta_to_inf_beta : forall x y, red_beta x y -> inf_beta x y.
Proof.
  unfold inf_beta; unfold red_beta.
  eauto using lem_star_to_inf, lem_step_beta_morphism.
Qed.

Lemma lem_step_beta_to_inf_beta : forall x y, step_beta x y -> inf_beta x y.
Proof.
  Reconstr.reasy (@lem_step_beta_to_red_beta, @lem_red_beta_to_inf_beta) Reconstr.Empty.
Qed.

Lemma lem_inf_beta_app : forall x x' y y', inf_beta x x' -> inf_beta y y' -> inf_beta (app x y) (app x' y').
Proof.
  pose_red_beta; pose lem_inf_beta_refl; coinduction.
Qed.

Lemma lem_inf_beta_abs : forall x x', inf_beta x x' -> inf_beta (abs x) (abs x').
Proof.
  pose_red_beta; pose lem_inf_beta_refl; coinduction.
Qed.

Ltac pose_inf_beta := pose proof lem_inf_beta_refl; pose proof lem_inf_beta_trans;
                      pose proof lem_red_beta_to_inf_beta; pose proof lem_inf_beta_prepend;
                      pose proof lem_inf_beta_append; pose proof lem_inf_beta_append_step;
                      pose proof lem_inf_beta_app; pose proof lem_inf_beta_abs;
                      autounfold with shints in *.

(******************************************************************************)

Lemma lem_step_beta_not_bot : forall t s, t == bot -> ~(step_beta t s).
Proof.
  unfold not; intros t s Ht H.
  inversion H; sauto; pose_term_eq; yelles 2.
Qed.

Lemma lem_step_beta_not_var : forall t s n, t == (var n) -> ~(step_beta t s).
Proof.
  unfold not; intros t s n Ht H.
  inversion H; sauto; pose_term_eq; yelles 2.
Qed.

Lemma lem_step_beta_preserves_abs : forall t s t', t == (abs t') -> step_beta t s ->
                                                   exists s', s == abs s'/\ step_beta t' s'.
Proof.
  unfold not; intros t s t' Ht H.
  inversion H; sauto.
  - pose_term_eq; yelles 2.
  - fold step_beta in *; exists y.
    inversion Ht; subst; fold term_eq in *; try yelles 1.
    rewrite <- H3; pose_term_eq; yelles 1.
Qed.

Lemma lem_red_beta_preserves_bot : forall t s, t == bot -> red_beta t s -> s == bot.
Proof.
  intros t s Ht H.
  induction H.
  - pose_term_eq; eauto.
  - pose lem_step_beta_not_bot; yelles 1.
Qed.

Lemma lem_red_beta_preserves_var : forall t s n, t == (var n) -> red_beta t s -> s == (var n).
Proof.
  intros t s n Ht H.
  induction H.
  - pose_term_eq; eauto.
  - pose lem_step_beta_not_var; yelles 1.
Qed.

Lemma lem_red_beta_preserves_abs : forall t s t', t == (abs t') -> red_beta t s ->
                                                  exists s', s == (abs s') /\ red_beta t' s'.
Proof.
  intros t s t' Ht H.
  revert t' Ht.
  induction H.
  - pose_term_eq; pose_red_beta; eauto.
  - intros t' Hx.
    assert (exists y', y == abs y' /\ step_beta t' y') by
        (pose lem_step_beta_preserves_abs; pose_term_eq; scrush).
    pose_term_eq; pose_red_beta; ycrush.
Qed.

Lemma lem_red_beta_from_app :
  forall x y, red_beta x y ->
              forall t s, x == app t s ->
                          (exists t' s', red_beta t t' /\ red_beta s s' /\ y == app t' s') \/
                          exists z, red_beta t (abs z).
Proof.
  intros x y H.
  induction H; intros t s Hx.
  - rewrite Hx in *; pose_term_eq; pose_red_beta; left; ycrush.
  - inversion H; subst.
    + inversion H1; subst.
      right; exists t1; apply lem_red_beta_refl.
      rewrite Hx in *.
      pose_term_eq; ycrush.
    + fold step_beta in *.
      assert (HH: t == x0) by (pose_term_eq; ycrush).
      rewrite <- HH in *; clear HH.
      assert (HH: s == y0) by (pose_term_eq; ycrush).
      rewrite <- HH in *; clear HH.
      generalize (IHstar x' y' (lem_term_eq_refl (app x' y'))).
      intro HH; destruct HH; simp_hyps.
      * left; exists t'; exists s'; rewrite H2; pose_red_beta; ycrush.
      * pose_red_beta; ycrush.
    + fold step_beta in *.
      assert (HH: t == x0) by (pose_term_eq; ycrush).
      rewrite <- HH in *; clear HH.
      assert (HH: s == y0) by (pose_term_eq; ycrush).
      rewrite <- HH in *; clear HH.
      generalize (IHstar x' y' (lem_term_eq_refl (app x' y'))).
      intro HH; destruct HH; simp_hyps.
      * left; exists t'; exists s'; rewrite H2; pose_red_beta; ycrush.
      * pose_red_beta; ycrush.
    + yelles 1.
Qed.

Lemma lem_inf_beta_preserves_bot : forall t s, t == bot -> inf_beta t s -> s == bot.
Proof.
  pose proof lem_red_beta_preserves_bot.
  csolve on 3 using ycrush.
Qed.

Lemma lem_inf_beta_preserves_var : forall t s n, t == (var n) -> inf_beta t s -> s == (var n).
Proof.
  pose proof lem_red_beta_preserves_var.
  csolve on 4 using ycrush.
Qed.

Lemma lem_inf_beta_preserves_abs : forall t s t', t == (abs t') -> inf_beta t s ->
                                                  exists s', s == (abs s') /\ inf_beta t' s'.
Proof.
  csolve on 4 using auto.
  - pose proof lem_red_beta_preserves_abs; ycrush.
  - pose proof lem_red_beta_preserves_abs; ycrush.
  - pose proof lem_red_beta_preserves_abs; ycrush.
  - assert (exists y, x == y /\ red_beta t' y) by
        (pose proof lem_red_beta_preserves_abs; ycrush).
    assert (red_beta t' x) by (pose_red_beta; ycrush).
    fold inf_beta in *.
    assert (inf_beta t' x') by (pose_inf_beta; ycrush).
    pose_term_eq; ycrush.
Qed.

Lemma lem_inf_beta_from_app :
  forall x y, inf_beta x y ->
              forall t s, x == app t s ->
                          (exists t' s', inf_beta t t' /\ inf_beta s s' /\ y == app t' s') \/
                          exists z, red_beta t (abs z).
Proof.
  csolve on 2 using auto.
  - intros t s Hx.
    generalize (lem_red_beta_from_app x bot H0 t s Hx).
    pose_inf_beta; ycrush.
  - intros t s Hx.
    generalize (lem_red_beta_from_app x (var n) H0 t s Hx).
    pose_inf_beta; ycrush.
  - intros t s Hx.
    fold inf_beta in *.
    generalize (lem_red_beta_from_app x (app x0 y0) H0 t s Hx).
    intro HH; destruct HH; simp_hyps.
    + assert (HH: x0 == t') by ycrush.
      rewrite HH in *; clear HH.
      assert (HH: y0 == s') by ycrush.
      rewrite HH in *; clear HH.
      left; exists x'; exists y'.
      pose_inf_beta; ycrush.
    + pose_inf_beta; ycrush.
  - intros t s Hx.
    generalize (lem_red_beta_from_app x (abs x0) H0 t s Hx).
    pose_inf_beta; ycrush.
Qed.

(******************************************************************************)

Lemma lem_inf_beta_preserves_rnf : forall t s, is_rnf t -> inf_beta t s -> is_rnf s.
Proof.
  intros t s H; unfold is_rnf in H; repeat ysplit; yisolve; intros H1.
  - unfold is_rnf; sauto.
    + assert (red_beta (var n) bot) by ycrush.
      assert (var n == bot) by (pose lem_red_beta_preserves_var; pose_term_eq; ycrush).
      ycrush.
    + assert (red_beta (var n) (app x y)) by ycrush.
      assert (var n == app x y) by (pose lem_red_beta_preserves_var; pose_term_eq; ycrush).
      ycrush.
  - generalize (lem_inf_beta_from_app (app t1 t2) s H1 t1 t2 (lem_term_eq_refl (app t1 t2))).
    unfold is_rnf; sauto.
    + assert (HH: s1 == t') by ycrush.
      rewrite HH in *; clear HH.
      assert (HH: s2 == s') by ycrush.
      rewrite HH in *; clear HH.
      pose_inf_beta; ycrush.
    + assert (inf_beta t1 (abs z)).
      econstructor; [ eauto | pose_inf_beta; ycrush ].
      ycrush.
    + assert (inf_beta t1 (abs z)).
      econstructor; [ eauto | pose_inf_beta; ycrush ].
      ycrush.
  - generalize (lem_inf_beta_preserves_abs (abs t) s t (lem_term_eq_refl (abs t)) H1).
    unfold is_rnf; sauto.
Qed.

(******************************************************************************)

Lemma lem_step_beta_shift :
  forall t s, step_beta t s -> forall d c t0, t == shift d c t0 ->
                                              exists s0, s == shift d c s0 /\ step_beta t0 s0.
Proof.
  induction 1.
  - inversion_clear H; intros.
    rewrite H0 in *; clear H0.
    destruct t0; autorewrite with shints in *; sauto.
    inversion H; subst; yisolve; fold term_eq in *.
    destruct t0_1; autorewrite with shints in *; sauto.
    inversion H4; subst; yisolve; fold term_eq in *.
    exists (t0_1 [0 := t0_2]).
    rewrite H1.
    rewrite H3.
    rewrite H6.
    split.
    + generalize (lem_shift_subst_2 d c 0 t0_1 t0_2); sauto.
    + Reconstr.reasy (@lem_step_beta_redex) Reconstr.Empty.
  - intros.
    rewrite H0 in *; clear H0.
    destruct t0; autorewrite with shints in *; sauto.
    inversion H1; subst; yisolve; fold term_eq in *.
    generalize (IHcomp_clos d c t0_1 H4); intro HH; destruct HH as [x0 [HH1 HH2]].
    exists (app x0 t0_2).
    rewrite H6.
    rewrite HH1.
    autorewrite with shints.
    pose_term_eq; ycrush.
  - intros.
    rewrite H0 in *; clear H0.
    destruct t0; autorewrite with shints in *; sauto.
    inversion H1; subst; yisolve; fold term_eq in *.
    generalize (IHcomp_clos d c t0_2 H6); intro HH; destruct HH as [y0 [HH1 HH2]].
    exists (app t0_1 y0).
    rewrite H4.
    rewrite HH1.
    autorewrite with shints.
    pose_term_eq; ycrush.
  - intros.
    destruct t0; autorewrite with shints in *; sauto.
    inversion H0; subst; yisolve; fold term_eq in *.
    generalize (IHcomp_clos d (c + 1) t0 H3); intro HH; destruct HH as [x0 [HH1 HH2]].
    exists (abs x0).
    rewrite HH1.
    autorewrite with shints.
    pose_term_eq; ycrush.
Qed.

Lemma lem_red_beta_shift :
  forall t s, red_beta t s -> forall d c t0, t == shift d c t0 ->
                                             exists s0, s == shift d c s0 /\ red_beta t0 s0.
Proof.
  induction 1.
  - pose_red_beta; pose_term_eq; pose lem_step_beta_shift; ycrush.
  - destruct t0; autorewrite with shints in *; sauto.
    + Reconstr.reasy (@lem_step_beta_not_bot) Reconstr.Empty.
    + Reconstr.reasy (@lem_step_beta_not_var) Reconstr.Empty.
    + Reconstr.reasy (@lem_step_beta_not_var) Reconstr.Empty.
    + generalize (lem_step_beta_shift x y H d c (app t0_1 t0_2)); intro HH; destruct HH as [x0 [HH1 HH2]];
        autorewrite with shints; eauto.
      pose_red_beta; pose_term_eq; ycrush.
    + generalize (lem_step_beta_shift x y H d c (abs t0)); intro HH; destruct HH as [x0 [HH1 HH2]];
        autorewrite with shints; eauto.
      pose_red_beta; pose_term_eq; ycrush.
Qed.
