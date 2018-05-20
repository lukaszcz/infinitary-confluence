
Require Import defs.
Require Import tactics.

(************************************************************************************************)

Definition peek (t : term) :=
  match t with
  | bot => bot
  | var n => var n
  | app x y => app x y
  | abs x => abs x
  end.

Lemma lem_peek_eq : forall t, t = peek t.
Proof.
  unfold peek; sauto.
Qed.

Ltac peek_tac := intros; rewrite lem_peek_eq at 1; unfold peek; sauto.

Lemma lem_shift_simpl_bot : forall d c, shift d c bot = bot.
Proof.
  peek_tac.
Qed.

Lemma lem_shift_simpl_var : forall d c n, shift d c (var n) = var (if c <=? n then n + d else n).
Proof.
  peek_tac.
Qed.

Lemma lem_shift_simpl_app : forall d c t1 t2, shift d c (app t1 t2) = app (shift d c t1) (shift d c t2).
Proof.
  peek_tac.
Qed.

Lemma lem_shift_simpl_abs : forall d c t, shift d c (abs t) = abs (shift d (c+1) t).
Proof.
  peek_tac.
Qed.

Hint Rewrite lem_shift_simpl_bot lem_shift_simpl_var lem_shift_simpl_app lem_shift_simpl_abs : shints.

Lemma lem_subst_simpl_bot : forall n x, subst n x bot = bot.
Proof.
  peek_tac.
Qed.

Lemma lem_subst_simpl_var :
  forall n s m, subst n s (var m) =
                if n <? m then var (m - 1) else if n =? m then shift n 0 s else var m.
Proof.
  peek_tac.
Qed.

Lemma lem_subst_simpl_app : forall n x t1 t2, subst n x (app t1 t2) = app (subst n x t1) (subst n x t2).
Proof.
  peek_tac.
Qed.

Lemma lem_subst_simpl_abs : forall n x t, subst n x (abs t) = abs (subst (n + 1) x t).
Proof.
  peek_tac.
Qed.

Hint Rewrite lem_subst_simpl_bot lem_subst_simpl_var lem_subst_simpl_app lem_subst_simpl_abs : shints.

(************************************************************************************************)

Lemma lem_par_clos_refl : forall R, reflexive term (par_clos R).
Proof.
  unfold reflexive; apply par_clos_refl.
Qed.

Lemma lem_par_clos_sym : forall R, symmetric term R -> symmetric term (par_clos R).
Proof.
  coinduction.
Qed.

Lemma lem_term_eq_refl : reflexive term term_eq.
Proof.
  sauto.
Qed.

Lemma lem_term_eq_sym : symmetric term term_eq.
Proof.
  assert (symmetric term (fun _ _ => False)) by scrush.
  pose lem_par_clos_sym; scrush.
Qed.

Lemma lem_term_eq_trans : transitive term term_eq.
Proof.
  coinduction.
Qed.

Lemma lem_term_eq_app : forall x y x' y', x == x' -> y == y' -> app x y == app x' y'.
Proof.
  coinduction.
Qed.

Lemma lem_term_eq_abs : forall x y, x == y -> abs x == abs y.
Proof.
  coinduction.
Qed.

Ltac pose_term_eq := pose proof lem_term_eq_app; pose proof lem_term_eq_abs;
                     pose proof lem_term_eq_refl; pose proof lem_term_eq_sym; pose proof lem_term_eq_trans;
                     autounfold with shints in *.

Add Parametric Relation : term term_eq
    reflexivity proved by (lem_term_eq_refl)
    symmetry proved by (lem_term_eq_sym)
    transitivity proved by (lem_term_eq_trans)
as term_eq_rel.

Add Parametric Morphism : app with
    signature term_eq ==> term_eq ==> term_eq as app_mor.
Proof.
  eauto using lem_term_eq_app.
Qed.

Add Parametric Morphism : abs with
    signature term_eq ==> term_eq as abs_mor.
Proof.
  eauto using lem_term_eq_abs.
Qed.

Add Parametric Morphism : beta_redex with
    signature term_eq ==> term_eq ==> iff as beta_redex_mor.
Proof.
  pose_term_eq; sauto; eapply beta_redex_c; eauto.
Qed.

Lemma lem_beta_redex_morphism : morphism beta_redex.
Proof.
  unfold morphism; intros.
  rewrite <- H0.
  rewrite <- H1.
  auto.
Qed.

Lemma lem_shift_mor : forall d c t t', t == t' -> shift d c t == shift d c t'.
Proof.
  coinduction.
Qed.

Lemma lem_subst_mor_0 : forall n t s s', s == s' -> t[n := s] == t[n := s'].
Proof.
  pose lem_shift_mor; coinduction on 1.
Qed.

Lemma lem_subst_mor : forall n t s t' s', t == t' -> s == s' -> t[n := s] == t'[n := s'].
Proof.
  pose lem_subst_mor_0; coinduction.
Qed.

Add Parametric Morphism (n m : nat) : (shift n m) with
    signature term_eq ==> term_eq as shift_mor.
Proof.
  eauto using lem_shift_mor.
Qed.

Add Parametric Morphism (n : nat) : (subst n) with
    signature term_eq ==> term_eq ==> term_eq as subst_mor.
Proof.
  eauto using lem_subst_mor.
Qed.
