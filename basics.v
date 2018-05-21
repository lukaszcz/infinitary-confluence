
Require Export defs.
Require Export tactics.
Require Export star.
Require Export equality.

Section Basic_clos_props.

Variable R : relation term.
Variable MorR : morphism R.

Lemma lem_comp_morphism : morphism (comp_clos R).
Proof.
  unfold morphism.
  intros x y H.
  induction H; intros x0 y0 Heq1 Heq2.
  - constructor; pose_term_eq; sauto.
  - rewrite H0 in Heq1.
    inversion Heq1; subst; intuition; fold term_eq in *;
      inversion Heq2; subst; intuition; fold term_eq in *;
        solve [ constructor; pose_term_eq; eauto ].
  - rewrite H0 in Heq1.
    inversion Heq1; subst; intuition; fold term_eq in *;
      inversion Heq2; subst; intuition; fold term_eq in *;
        solve [ constructor; pose_term_eq; eauto ].
  - inversion Heq1; subst; intuition; fold term_eq in *;
      inversion Heq2; subst; intuition; fold term_eq in *;
        solve [ constructor; pose_term_eq; eauto ].
Qed.

Add Parametric Morphism : (comp_clos R) with
    signature term_eq ==> term_eq ==> iff as comp_mor.
Proof.
  split; intro; eapply lem_comp_morphism; pose_term_eq; eauto.
Qed.

Add Parametric Morphism : (star R) with
    signature term_eq ==> term_eq ==> iff as star_mor.
Proof.
  split; intro; eapply lem_star_morphism; pose_term_eq; eauto.
Qed.

Lemma lem_inf_morphism : morphism (inf_clos (star R)).
Proof.
  assert (Hm: morphism (star R)) by eauto using lem_star_morphism.
  unfold morphism.
  coinduction H using auto.
  - intros x1 y1 Heq1 Heq2.
    inversion Heq2; subst; intuition; fold term_eq in *; econstructor; pose_term_eq; eauto.
  - intros x1 y1 Heq1 Heq2.
    inversion Heq2; subst; intuition; fold term_eq in *; econstructor; pose_term_eq; eauto.
  - intros x1 y1 Heq1 Heq2.
    inversion Heq2; subst; intuition; fold term_eq in *; econstructor; pose_term_eq; eauto.
  - intros x1 y1 Heq1 Heq2.
    inversion Heq2; subst; intuition; fold term_eq in *; econstructor; pose_term_eq; eauto.
Qed.

Lemma lem_inf_refl : reflexive term (inf_clos (star R)).
Proof.
  pose_star; coinduction on 0.
Qed.

Lemma lem_inf_prepend : forall x y z, star R x y -> inf_clos (star R) y z -> inf_clos (star R) x z.
Proof.
  pose_star; csolve on 4.
Qed.

Lemma lem_star_to_inf : forall x y, star R x y -> inf_clos (star R) x y.
Proof.
  Reconstr.reasy (lem_inf_refl, lem_inf_prepend) (reflexive).
Qed.

Lemma lem_inf_subset (S : relation term) : (forall x y, R x y -> S x y) ->
                       forall x y, inf_clos (star R) x y -> inf_clos (star S) x y.
Proof.
  pose_star; coinduction using eauto.
Qed.

Lemma lem_comp_subst_closed : subst_closed R -> subst_closed (comp_clos R).
Proof.
  unfold subst_closed.
  intros H x x'.
  enough (comp_clos R x x' -> forall n y, comp_clos R (x [n := y]) (x' [n := y])) by scrush.
  intro H1; induction H1; intros; try rewrite H0; pose_term_eq; csolve.
Qed.

Lemma lem_comp_shift_closed : shift_closed R -> shift_closed (comp_clos R).
Proof.
  unfold shift_closed.
  intro H.
  enough (forall t t', comp_clos R t t' -> forall d c, comp_clos R (shift d c t) (shift d c t')) by scrush.
  intros t t' H1; induction H1; intros; try rewrite H0; pose_term_eq; csolve.
Qed.

Lemma lem_star_subst_closed : subst_closed R -> subst_closed (star R).
Proof.
  unfold subst_closed.
  intro H; sauto.
  induction H1; try rewrite H0; pose_star; eauto.
Qed.

Lemma lem_star_shift_closed : shift_closed R -> shift_closed (star R).
Proof.
  unfold shift_closed.
  intro H; sauto.
  induction H1; try rewrite H0; pose_star; eauto.
Qed.

Lemma lem_inf_shift_closed : shift_closed R -> shift_closed (inf_clos R).
Proof.
  unfold shift_closed.
  intro H0.
  coinduction H using auto.
  - autorewrite with shints.
    constructor.
    assert (shift d c bot = bot) by (autorewrite with shints; reflexivity).
    yelles 1.
  - clear H; autorewrite with shints; ysplit.
    + constructor.
      assert (shift d c (var n) = var (n + d)) by (autorewrite with shints; sauto).
      yelles 1.
    + constructor.
      assert (shift d c (var n) = var n) by (autorewrite with shints; sauto).
      yelles 1.
  - autorewrite with shints.
    apply inf_clos_app with (x := shift d c x) (y := shift d c y).
    + assert (app (shift d c x) (shift d c y) = shift d c (app x y)) by (autorewrite with shints; reflexivity).
      yelles 1.
    + auto.
    + auto.
  - autorewrite with shints.
    apply inf_clos_abs with (x := shift d (c + 1) x).
    + assert (abs (shift d (c + 1) x) = shift d c (abs x)) by (autorewrite with shints; reflexivity).
      yelles 1.
    + auto.
Qed.

End Basic_clos_props.

Lemma lem_inf_subst (R : relation term):
  morphism R -> subst_closed R -> shift_closed R ->
  forall s s' t t', inf_clos (star R) s s' -> inf_clos (star R) t t' ->
                    forall n, inf_clos (star R) (subst n t s) (subst n t' s').
Proof.
  intros Hm H0 H1.
  assert (Hs0: subst_closed (star R)) by auto using lem_star_subst_closed.
  clear H0; unfold subst_closed in Hs0.
  assert (Hs1: shift_closed (star R)) by auto using lem_star_shift_closed.
  clear H1; unfold shift_closed in Hs1.
  coinduction H using auto.
  - clear H; intros; autorewrite with shints.
    constructor.
    assert (HH: bot = bot [n := t]) by (autorewrite with shints; auto).
    rewrite HH; clear HH.
    eauto.
  - clear H; intros.
    assert (inf_clos (star R) (var n [n0 := t]) (var n [n0 := t'])).
    autorewrite with shints; repeat ysplit.
    + solve [ constructor; pose_star; sauto ].
    + generalize lem_inf_shift_closed; unfold shift_closed; auto.
    + solve [ constructor; pose_star; sauto ].
    + eapply lem_inf_prepend; sauto.
  - intros; autorewrite with shints.
    apply inf_clos_app with (x := x[n := t]) (y := y[n := t]).
    + assert (HH: app (x [n := t]) (y [n := t]) = (app x y) [n := t]) by
          (autorewrite with shints; reflexivity).
      rewrite HH.
      auto.
    + eauto.
    + eauto.
  - intros; autorewrite with shints.
    apply inf_clos_abs with (x := x [n + 1 := t]).
    + assert (HH: abs (x [n + 1 := t]) = abs x [n := t]) by
          (autorewrite with shints; reflexivity).
      rewrite HH.
      auto.
    + eauto.
Qed.

Definition appendable (R : relation term) :=
  forall t1 t2 t3, inf_clos R t1 t2 -> R t2 t3 -> inf_clos R t1 t3.

Lemma lem_inf_trans (R : relation term) : appendable R -> transitive term (inf_clos R).
Proof.
  unfold appendable; unfold transitive.
  intro Ha.
  coinduction H on 4 using eauto.
  - assert (HH: inf_clos R x (app x0 y0)) by eauto.
    inversion HH; subst.
    econstructor; eauto.
  - assert (HH: inf_clos R x (abs x0)) by eauto.
    inversion HH; subst.
    econstructor; eauto.
Qed.

Lemma lem_par_bot_to_sim (U : term -> Prop) :
  U bot -> forall x y, par_bot U x y -> sim U x y.
Proof.
  intro; coinduction using ssolve.
Qed.
