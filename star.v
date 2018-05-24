
Require Import tactics.
Require Import defs.
Require Import equality.

Section Star.

Variable R : relation term.
Variable MorR : morphism R.

Lemma lem_star_morphism : morphism (star R).
Proof.
  unfold morphism.
  induction 1; subst; intros.
  - apply star_refl; pose_term_eq; eauto.
  - eapply star_step; pose_term_eq; eauto.
Qed.

Add Parametric Morphism : (star R) with
    signature term_eq ==> term_eq ==> iff as star_n_mor.
Proof.
  split; intro; eapply lem_star_morphism; pose_term_eq; eauto.
Qed.

Lemma lem_star_refl : forall x, star R x x.
Proof.
  sauto; constructor; reflexivity.
Qed.

Lemma lem_star_trans :
  forall x y z, star R x y -> star R y z -> star R x z.
Proof.
  intros x y z H; revert z.
  induction H; sauto.
  - rewrite H; eauto.
  - Reconstr.reasy (@star_step) Reconstr.Empty.
Qed.

Lemma lem_star_step1 :
  forall x y, R x y -> star R x y.
Proof.
  pose_term_eq; reasy (@star_step, @star_refl) Reconstr.Empty.
Qed.

Lemma lem_star_subset (S : relation term) : 
  (forall x y, R x y -> S x y) -> forall x y, star R x y -> star S x y.
Proof.
  intros H0 x y H.
  induction H; sauto.
  - constructor; auto.
  - Reconstr.reasy (@star_step) Reconstr.Empty.
Qed.

Lemma lem_star_step : forall x y z, R x y -> star R y z -> star R x z.
Proof.
  scrush.
Qed.

End Star.

Ltac pose_star := pose proof @lem_star_refl; pose proof @lem_star_step;
                  pose proof @lem_star_trans; pose proof @lem_star_step1;
                  pose proof @lem_star_subset; pose proof lem_star_morphism; unfold morphism in *.
