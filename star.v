
Require Import tactics.
Require Import defs.
Require Import equality.

Section Star_n.

Variable R : relation term.
Variable MorR : morphism R.

Lemma lem_star_n_morphism : forall n, morphism (star_n R n).
Proof.
  unfold morphism.
  induction n; intros x y HH; inversion HH; subst; intros.
  - apply star_n_refl; pose_term_eq; eauto.
  - eapply star_n_step; pose_term_eq; eauto.
Qed.

Add Parametric Morphism (n : nat) : (star_n R n) with
    signature term_eq ==> term_eq ==> iff as star_n_mor.
Proof.
  split; intro; eapply lem_star_n_morphism; pose_term_eq; eauto.
Qed.

Lemma lem_star_n_trans :
  forall n m x y z, star_n R n x y -> star_n R m y z -> star_n R (n + m) x z.
Proof.
  intros n m x y z H; revert z.
  induction H; sauto.
  - rewrite H; eauto.
  - Reconstr.reasy (@star_n_step) Reconstr.Empty.
Qed.

Lemma lem_star_n_step1 :
  forall x y, R x y -> star_n R 1 x y.
Proof.
  pose_term_eq; reasy (@star_n_step, @star_n_refl) Reconstr.Empty.
Qed.

Lemma lem_star_n_subset (S : relation term) : 
  (forall x y, R x y -> S x y) -> forall n x y, star_n R n x y -> star_n S n x y.
Proof.
  intros H0 n x y H.
  induction H; sauto.
  - constructor; auto.
  - Reconstr.reasy (@star_n_step) Reconstr.Empty.
Qed.

End Star_n.

Ltac pose_star_n := pose proof @star_n_refl; pose proof @star_n_step;
                    pose proof @lem_star_n_trans; pose proof @lem_star_n_step1;
                    pose proof @lem_star_n_subset.

Section Star.

Variable R : relation term.
Variable MorR : morphism R.

Lemma lem_star_refl : forall x, star R x x.
Proof.
  Reconstr.reasy (@star_n_refl, lem_term_eq_refl) (@star).
Qed.

Lemma lem_star_step : forall x y z, R x y -> star R y z -> star R x z.
Proof.
  Reconstr.reasy (@star_n_step) (@star).
Qed.

Lemma lem_star_trans :
  forall x y z, star R x y -> star R y z -> star R x z.
Proof.
  unfold star; pose @lem_star_n_trans; scrush.
Qed.

Lemma lem_star_step1 :
  forall x y, R x y -> star R x y.
Proof.
  unfold star; pose_star_n; scrush.
Qed.

Lemma lem_star_subset (S : relation term) :
  (forall x y, R x y -> S x y) -> forall x y, star R x y -> star S x y.
Proof.
  unfold star; pose_star_n; scrush.
Qed.

Lemma lem_star_morphism : morphism (star R).
Proof.
  unfold morphism; unfold star.
  pose lem_star_n_morphism; pose_star_n; yelles 1.
Qed.

End Star.

Ltac pose_star := pose proof @lem_star_refl; pose proof @lem_star_step;
                  pose proof @lem_star_trans; pose proof @lem_star_step1;
                  pose proof @lem_star_subset; pose proof lem_star_morphism; unfold morphism in *.
