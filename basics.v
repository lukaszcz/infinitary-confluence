(* This file formalises some basic properties of the relations from
   Section 4, including lemmas 4.3, 4.4 and generalised versions of
   lemmas 4.5, 4.7. *)

Require Export defs.
Require Export tactics.
Require Export star.
Require Export equality.

Lemma lem_root_active_bot : root_active bot.
Proof.
  unfold root_active.
  unfold has_rnf.
  intro H.
  destruct H as [t [H1 H2]].
  revert H1.
  inversion_clear H2.
  - ycrush.
  - inversion_clear H; sauto; inversion_clear H0.
  - inversion_clear H; sauto; inversion_clear H0.
  - inversion_clear H; sauto; inversion_clear H0.
Qed.

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

(******************************************************************************)

Definition red R := star (comp_clos R).
Hint Unfold red.

Add Parametric Morphism : (red R) with
    signature term_eq ==> term_eq ==> iff as red_mor.
Proof.
  split; intro; eapply lem_star_morphism; pose lem_comp_morphism; pose_term_eq; eauto.
Qed.

Lemma lem_red_refl : forall x y, x == y -> red R x y.
Proof.
  yelles 2.
Qed.

Lemma lem_red_refl_0 : reflexive term (red R).
Proof.
  pose_term_eq; yelles 2.
Qed.

Lemma lem_red_trans : transitive term (red R).
Proof.
  generalize lem_comp_morphism; unfold transitive; pose_star; eauto.
Qed.

Lemma lem_red_step : forall x y z, comp_clos R x y -> red R y z -> red R x z.
Proof.
  generalize lem_comp_morphism; pose_star; eauto.
Qed.

Lemma lem_red_app_l : forall x x', red R x x' -> forall y, red R (app x y) (app x' y).
Proof.
  intros x x' H.
  induction H; intro.
  - rewrite H; apply lem_red_refl_0.
  - apply lem_red_step with (y := app y y0).
    + constructor 2; pose_term_eq; eauto.
    + auto.
Qed.

Lemma lem_red_app_r : forall y y', red R y y' -> forall x, red R (app x y) (app x y').
Proof.
  intros y y' H.
  induction H; intro.
  - rewrite H; apply lem_red_refl_0.
  - apply lem_red_step with (y := app x0 y).
    + constructor 3; pose_term_eq; eauto.
    + auto.
Qed.

Lemma lem_red_app : forall x x' y y', red R x x' -> red R y y' ->
                                      red R (app x y) (app x' y').
Proof.
  eauto using lem_red_app_l, lem_red_app_r, lem_red_trans.
Qed.

Lemma lem_red_abs : forall x x', red R x x' -> red R (abs x) (abs x').
Proof.
  intros x x' H.
  induction H.
  - rewrite H; apply lem_red_refl_0.
  - apply lem_red_step with (y := abs y); csolve.
Qed.

Lemma lem_red_step_rev : forall x y z, red R x y -> comp_clos R y z -> red R x z.
Proof.
  intros x y z H.
  revert z.
  induction H.
  - intros; rewrite H; econstructor 2; [ eauto | constructor; pose_term_eq; eauto ].
  - eauto using lem_red_step.
Qed.

Lemma lem_step_to_red : forall x y, comp_clos R x y -> red R x y.
Proof.
  intros; eapply lem_red_step; eauto using lem_red_refl_0.
Qed.

(******************************************************************************)

Lemma lem_inf_morphism : morphism (inf_clos (star R)).
Proof.
  assert (Hm: morphism (star R)) by eauto using lem_star_morphism.
  unfold morphism.
  enough (forall x y, inf_clos (star R) x y ->
                      forall x' y', y == y' -> x == x' ->
                                    inf_clos (star R) x' y') by ycrush.
  coinduct CH; intros x1 y1 Heq1 Heq2;
    inversion Heq1; subst; intuition; fold term_eq in *; econstructor; pose_term_eq; eauto.
Qed.

Lemma lem_inf_refl_0 : reflexive term (inf_clos (star R)).
Proof.
  pose_star; coinduction on 0.
Qed.

(* Lemma 4.3, (1) *)
Lemma lem_inf_refl : forall x y, x == y -> inf_clos (star R) x y.
Proof.
  pose_star; pose_term_eq; coinduction on 0.
Qed.

(* Lemma 4.3, (2) *)
Lemma lem_inf_prepend : forall x y z, star R x y -> inf_clos (star R) y z -> inf_clos (star R) x z.
Proof.
  pose_star; csolve on 4.
Qed.

(* Lemma 4.3, (3) *)
Lemma lem_star_to_inf : forall x y, star R x y -> inf_clos (star R) x y.
Proof.
  Reconstr.reasy (lem_inf_refl_0, lem_inf_prepend) (reflexive).
Qed.

(* Lemma 4.4 *)
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
  induction H0; try rewrite H0; pose_star; eauto.
Qed.

Lemma lem_star_shift_closed : shift_closed R -> shift_closed (star R).
Proof.
  unfold shift_closed.
  intro H; sauto.
  induction H0; try rewrite H0; pose_star; eauto.
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

(******************************************************************************)

(* Lemma 4.5, generalised *)
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
  coinduct H.
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

(* Lemma 6.2, generalised Lemma 4.7 *)
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

Lemma lem_inf_reflexive (R : relation term) : reflexive term R -> reflexive term (inf_clos R).
Proof.
  intro; coinduction on 0.
Qed.

Lemma lem_R_to_inf (R : relation term) : morphism R -> reflexive term R ->
  forall x y, R x y -> inf_clos R x y.
Proof.
  intros Hm Hr.
  pose lem_inf_reflexive; coinduction CH on 1.
Qed.

Lemma lem_inf_to_aux (R : relation term) : morphism R ->
  forall x y, inf_clos (star R) x y -> aux_clos R x y.
Proof.
  unfold aux_clos.
  pose lem_inf_morphism; pose lem_R_to_inf; pose lem_inf_refl_0; ycrush.
Qed.

Lemma lem_inf_prepend_step (R : relation term) :
  transitive term R -> forall x y z, R x y -> inf_clos R y z -> inf_clos R x z.
Proof.
  csolve on 5.
Qed.

Lemma lem_aux_to_inf (R : relation term) :
  appendable (star R) -> forall x y, aux_clos R x y -> inf_clos (star R) x y.
Proof.
  intros Ha.
  unfold aux_clos.
  coinduction CH using eauto.
  - inversion H0; subst.
    assert (inf_clos (inf_clos (star R)) x1 x') by (pose lem_inf_prepend_step; pose lem_inf_trans; ycrush).
    assert (inf_clos (inf_clos (star R)) y y') by (pose lem_inf_prepend_step; pose lem_inf_trans; ycrush).
    cosolve CH.
  - inversion H0; subst.
    assert (inf_clos (inf_clos (star R)) x1 x') by (pose lem_inf_prepend_step; pose lem_inf_trans; ycrush).
    cosolve CH.
Qed.
