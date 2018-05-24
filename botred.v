Require Import beta.
Require Import cases.

Section Botred.

Variable U : term -> Prop.
Variable Hm : meaningless U.

(************************************************************************************************)

Lemma lem_par_bot_refl_0 : forall x, par_bot U x x.
Proof.
  coinduction on 0.
Qed.

Lemma lem_par_bot_refl : forall x y, x == y -> par_bot U x y.
Proof.
  coinduction.
Qed.

Lemma lem_par_bot_preserves_U : forall t s, U t -> par_bot U t s -> U s.
Proof.
  pose lem_par_bot_to_sim; ycrush.
Qed.

Lemma lem_par_bot_preserves_U_rev : forall t s, U t -> par_bot U s t -> U s.
Proof.
  pose lem_par_bot_to_sim; pose lem_sim_sym; unfold symmetric in *; ycrush.
Qed.

Lemma lem_par_bot_preserves_bot_redex_rev :
  forall x y z, par_bot U x y -> bot_redex U y z -> bot_redex U x z.
Proof.
  unfold bot_redex; pose lem_par_bot_preserves_U_rev; ycrush.
Qed.

Lemma lem_par_bot_trans : transitive term (par_bot U).
Proof.
  coinduction CH on 4 using auto.
  - clear CH; pose lem_par_bot_preserves_bot_redex_rev; ycrush.
  - revert H; csolve CH using eauto.
    unfold bot_redex in *; clear CH; ycrush.
  - revert H; csolve CH using eauto.
    unfold bot_redex in *; clear CH; ycrush.
Qed.

Lemma lem_step_bot_to_par_bot : forall t s, step_bot U t s -> par_bot U t s.
Proof.
  pose lem_par_bot_refl; coinduction.
Qed.

Lemma lem_par_bot_app :
  forall t s1 s2, par_bot U t (app s1 s2) ->
                  exists t1 t2, t = app t1 t2 /\ par_bot U t1 s1 /\ par_bot U t2 s2.
Proof.
  destruct t; intros ? ? H; inversion H; subst; ycrush.
Qed.

Lemma lem_par_bot_abs :
  forall t s, par_bot U t (abs s) ->
                  exists u, t = abs u /\ par_bot U u s.
Proof.
  destruct t; intros ? H; inversion H; subst; ycrush.
Qed.

(************************************************************************************************)

Lemma lem_U_morphism : forall x y, U x -> x == y -> U y.
Proof.
  intros.
  assert (inf_beta x y) by (pose_inf_beta; ycrush).
  sauto.
Qed.

Lemma lem_bot_redex_morphism : morphism (bot_redex U).
Proof.
  unfold morphism, bot_redex.
  pose lem_U_morphism; pose_term_eq; ycrush.
Qed.

Lemma lem_par_bot_morphism : morphism (par_bot U).
Proof.
  unfold morphism.
  coinduct CH.
  - clear CH; pose lem_bot_redex_morphism; ycrush.
  - revert H; csolve CH.
  - revert H; csolve CH.
  - intros x1 y1 Ha1 Ha2;
      inversion Ha1; subst; try solve [ clear CH; exfalso; auto ];
        inversion Ha2; subst; try solve [ clear CH; exfalso; auto ].
    fold term_eq in *.
    constructor 4.
    + apply CH with (x := x0) (y := x'); pose_term_eq; eauto.
    + pose_term_eq; ycrush.
  - clear H0; revert H; cintro.
    + clear CH; sauto.
    + destruct x', y'; try solve [ clear CH; sauto ].
      pose_term_eq; cosolve CH.
Qed.

Add Parametric Morphism : (bot_redex U) with
    signature term_eq ==> term_eq ==> iff as bot_redex_mor.
Proof.
  split; intro; eapply lem_bot_redex_morphism; pose_term_eq; eauto.
Qed.

Add Parametric Morphism : (par_bot U) with
    signature term_eq ==> term_eq ==> iff as par_bot_mor.
Proof.
  split; intro; eapply lem_par_bot_morphism; pose_term_eq; eauto.
Qed.

Lemma lem_bot_redex_shift_closed : shift_closed (bot_redex U).
Proof.
  unfold shift_closed, bot_redex.
  sintuition.
  - sauto.
  - destruct t; autorewrite with shints in *; pose_term_eq; yelles 1.
  - rewrite H2; autorewrite with shints in *; yelles 1.
Qed.

Lemma lem_par_bot_shift_closed : shift_closed (par_bot U).
Proof.
  pose lem_bot_redex_shift_closed; unfold shift_closed.
  coinduction.
Qed.

Lemma lem_bot_redex_subst : forall t t' s s', bot_redex U t t' ->
                                              forall n, bot_redex U (t[n := s]) (t'[n := s']) \/
                                                        (t = var n /\ s == bot).
Proof.
  unfold bot_redex.
  intros; simp_hyps.
  assert (Hr1: U (t [n := s])) by sauto.
  assert (Hr3: t' [n := s'] == bot) by (rewrite H1; autorewrite with shints in *; yelles 1).
  destruct t eqn:?; autorewrite with shints in *; try solve [ pose_term_eq; left; yelles 1 ].
  repeat ysplit.
  - left; sauto.
  - destruct s eqn:?; autorewrite with shints in *; try solve [ pose_term_eq; left; yelles 1 ].
    right; split.
    + bomega.
    + reflexivity.
  - left; sauto.
Qed.

Lemma lem_par_bot_subst : forall t t' s s', par_bot U t t' -> par_bot U s s' ->
                                            forall n, par_bot U (t [n := s]) (t' [n := s']).
Proof.
  coinduction CH using auto.
  - clear CH; intros.
    generalize (lem_bot_redex_subst t t' s s' H0 n).
    sintuition.
    assert (HH: t' == bot) by ycrush.
    rewrite HH.
    rewrite H4.
    autorewrite with shints; repeat ysplit; try bomega.
    ycrush.
  - clear CH; intros; autorewrite with shints; repeat ysplit; try bomega.
    + eauto using lem_par_bot_refl_0.
    + eauto using lem_par_bot_shift_closed.
Qed.

(************************************************************************************************)

Lemma lem_beta_bot_redex_morphism : morphism (beta_bot_redex U).
Proof.
  unfold morphism, beta_bot_redex.
  pose lem_beta_redex_morphism; pose lem_bot_redex_morphism; ycrush.
Qed.

Lemma lem_step_beta_bot_morphism : morphism (step_beta_bot U).
Proof.
  unfold step_beta_bot.
  apply lem_comp_morphism.
  apply lem_beta_bot_redex_morphism.
Qed.

Lemma lem_red_beta_bot_morphism : morphism (red_beta_bot U).
Proof.
  unfold red_beta.
  apply lem_star_morphism.
  apply lem_step_beta_bot_morphism.
Qed.

Lemma lem_inf_beta_bot_morphism : morphism (inf_beta_bot U).
Proof.
  unfold inf_beta.
  apply lem_inf_morphism.
  apply lem_step_beta_bot_morphism.
Qed.

Add Parametric Morphism : (beta_bot_redex U) with
    signature term_eq ==> term_eq ==> iff as beta_bot_redex_mor.
Proof.
  split; intro; eapply lem_beta_bot_redex_morphism; pose_term_eq; eauto.
Qed.

Add Parametric Morphism : (step_beta_bot U) with
    signature term_eq ==> term_eq ==> iff as step_beta_bot_mor.
Proof.
  split; intro; eapply lem_step_beta_bot_morphism; pose_term_eq; eauto.
Qed.

Add Parametric Morphism : (red_beta_bot U) with
    signature term_eq ==> term_eq ==> iff as red_beta_bot_mor.
Proof.
  split; intro; eapply lem_red_beta_bot_morphism; pose_term_eq; eauto.
Qed.

Add Parametric Morphism : (inf_beta_bot U) with
    signature term_eq ==> term_eq ==> iff as inf_beta_bot_mor.
Proof.
  split; intro; eapply lem_inf_beta_bot_morphism; pose_term_eq; eauto.
Qed.

(************************************************************************************************)

Lemma lem_step_beta_bot_redex_beta : forall x y, step_beta_bot U (app (abs x) y) (x [0 := y]).
Proof.
  constructor; constructor; econstructor; pose_term_eq; eauto.
Qed.

Lemma lem_step_beta_bot_redex_bot : forall x, U x -> x != bot -> step_beta_bot U x bot.
Proof.
  constructor; constructor 2; econstructor; pose_term_eq; eauto.
Qed.

Lemma lem_red_beta_bot_refl : forall x y, x == y -> red_beta_bot U x y.
Proof.
  apply lem_red_refl; apply lem_beta_bot_redex_morphism.
Qed.

Lemma lem_red_beta_bot_refl_0 : reflexive term (red_beta_bot U).
Proof.
  apply lem_red_refl_0; apply lem_beta_bot_redex_morphism.
Qed.

Lemma lem_red_beta_bot_trans : transitive term (red_beta_bot U).
Proof.
  apply lem_red_trans; apply lem_beta_bot_redex_morphism.
Qed.

Lemma lem_red_beta_bot_step : forall x y z, step_beta_bot U x y -> red_beta_bot U y z -> red_beta_bot U x z.
Proof.
  apply lem_red_step; apply lem_beta_bot_redex_morphism.
Qed.

Lemma lem_red_beta_bot_app : forall x x' y y', red_beta_bot U x x' -> red_beta_bot U y y' ->
                                               red_beta_bot U (app x y) (app x' y').
Proof.
  apply lem_red_app; apply lem_beta_bot_redex_morphism.
Qed.

Lemma lem_red_beta_bot_abs : forall x x', red_beta_bot U x x' -> red_beta_bot U (abs x) (abs x').
Proof.
  apply lem_red_abs; apply lem_beta_bot_redex_morphism.
Qed.

Lemma lem_red_beta_bot_step_rev : forall x y z, red_beta_bot U x y -> step_beta_bot U y z -> red_beta_bot U x z.
Proof.
  apply lem_red_step_rev; apply lem_beta_bot_redex_morphism.
Qed.

Lemma lem_red_beta_bot_redex_beta : forall x y, red_beta_bot U (app (abs x) y) (x [0 := y]).
Proof.
  intros; econstructor 2.
  - eauto using lem_step_beta_bot_redex_beta.
  - constructor; pose_term_eq; eauto.
Qed.

Lemma lem_red_beta_bot_redex_bot : forall x y, bot_redex U x y -> red_beta_bot U x y.
Proof.
  unfold bot_redex.
  intros; simp_hyps; econstructor 2.
  - eauto using lem_step_beta_bot_redex_bot.
  - constructor; pose_term_eq; eauto.
Qed.

Lemma lem_red_beta_bot_redex_U : forall t, U t -> red_beta_bot U t bot.
Proof.
  intros t H.
  assert (HH: bot_redex U t bot \/ t = bot) by
      (unfold bot_redex; destruct t; eauto; left; ycrush).
  destruct HH.
  - apply lem_red_beta_bot_redex_bot; assumption.
  - apply lem_red_beta_bot_refl; ycrush.
Qed.

Lemma lem_step_beta_bot_to_red_beta_bot : forall x y, step_beta_bot U x y -> red_beta_bot U x y.
Proof.
  apply lem_step_to_red; apply lem_beta_bot_redex_morphism.
Qed.

Lemma lem_step_beta_to_step_beta_bot : forall x y, step_beta x y -> step_beta_bot U x y.
Proof.
  induction 1; ycrush.
Qed.

Lemma lem_step_beta_to_red_beta_bot : forall x y, step_beta x y -> red_beta_bot U x y.
Proof.
  pose lem_step_beta_to_step_beta_bot; pose lem_step_to_red; pose lem_beta_bot_redex_morphism.
  unfold red_beta_bot, step_beta_bot, step_beta, red in *.
  ycrush.
Qed.

Lemma lem_red_beta_to_red_beta_bot : forall x y, red_beta x y -> red_beta_bot U x y.
Proof.
  intros x y H.
  induction H.
  - ycrush.
  - pose lem_step_beta_to_red_beta_bot; pose lem_red_beta_bot_trans; ycrush.
Qed.

Ltac pose_red_beta_bot :=
  pose proof lem_red_beta_bot_refl_0; pose proof lem_red_beta_bot_refl; pose proof lem_red_beta_bot_trans;
  pose proof lem_red_beta_bot_step; pose proof lem_red_beta_bot_step_rev;
  pose proof lem_red_beta_bot_redex_beta; pose proof lem_red_beta_bot_redex_bot;
  pose proof lem_step_beta_bot_to_red_beta_bot; pose proof lem_red_beta_to_red_beta_bot;
  pose proof lem_step_beta_to_red_beta_bot; pose proof lem_step_beta_to_step_beta_bot;
  pose proof lem_red_beta_bot_app; pose proof lem_red_beta_bot_abs;
  pose proof lem_red_beta_bot_redex_U;
  autounfold with shints in *.

(******************************************************************************)

Lemma lem_beta_bot_redex_shift_closed : shift_closed (beta_bot_redex U).
Proof.
  unfold beta_bot_redex, shift_closed.
  pose lem_beta_redex_shift_closed; pose lem_bot_redex_shift_closed; ycrush.
Qed.

Lemma lem_step_beta_bot_shift_closed : shift_closed (step_beta_bot U).
Proof.
  unfold step_beta_bot.
  pose lem_beta_bot_redex_morphism; pose lem_comp_shift_closed; pose lem_beta_bot_redex_shift_closed; scrush.
Qed.

Lemma lem_red_beta_bot_shift_closed : shift_closed (red_beta_bot U).
Proof.
  unfold red_beta.
  pose lem_step_beta_bot_morphism; pose lem_star_shift_closed; pose lem_step_beta_bot_shift_closed; scrush.
Qed.

Lemma lem_inf_beta_bot_shift_closed : shift_closed (inf_beta_bot U).
Proof.
  pose lem_inf_shift_closed; pose lem_red_beta_bot_shift_closed; scrush.
Qed.

Lemma lem_inf_beta_bot_refl : reflexive term (inf_beta_bot U).
Proof.
  unfold inf_beta_bot, red_beta_bot; pose lem_inf_refl_0; scrush.
Qed.

Lemma lem_inf_beta_bot_prepend : forall x y z, red_beta_bot U x y -> inf_beta_bot U y z -> inf_beta_bot U x z.
Proof.
  unfold inf_beta_bot, red_beta_bot.
  pose lem_step_beta_bot_morphism; pose lem_inf_prepend; eauto.
Qed.

Lemma lem_inf_beta_bot_prepend_red_beta :
  forall x y z, red_beta x y -> inf_beta_bot U y z -> inf_beta_bot U x z.
Proof.
  Reconstr.reasy (lem_red_beta_to_red_beta_bot, lem_inf_beta_bot_prepend) Reconstr.Empty.
Qed.

Lemma lem_red_beta_bot_to_inf_beta_bot : forall x y, red_beta_bot U x y -> inf_beta_bot U x y.
Proof.
  unfold inf_beta_bot, red_beta_bot.
  eauto using lem_star_to_inf, lem_step_beta_bot_morphism.
Qed.

Lemma lem_inf_beta_bot_app :
  forall x x' y y', inf_beta_bot U x x' -> inf_beta_bot U y y' -> inf_beta_bot U (app x y) (app x' y').
Proof.
  pose_red_beta_bot; pose lem_inf_beta_bot_refl; coinduction.
Qed.

Lemma lem_inf_beta_bot_abs : forall x x', inf_beta_bot U x x' -> inf_beta_bot U (abs x) (abs x').
Proof.
  pose_red_beta_bot; pose lem_inf_beta_bot_refl; coinduction.
Qed.

Lemma lem_inf_beta_to_inf_beta_bot : forall x y, inf_beta x y -> inf_beta_bot U x y.
Proof.
  unfold inf_beta, inf_beta_bot, red_beta, red_beta_bot.
  pose lem_step_beta_to_step_beta_bot; pose lem_inf_subset; ycrush.
Qed.

Ltac pose_inf_beta_bot := pose proof lem_inf_beta_bot_refl; pose proof lem_inf_beta_to_inf_beta_bot;
                          pose proof lem_red_beta_bot_to_inf_beta_bot; pose proof lem_inf_beta_bot_prepend;
                          pose proof lem_inf_beta_bot_prepend_red_beta;
                          pose proof lem_inf_beta_bot_app; pose proof lem_inf_beta_bot_abs;
                          autounfold with shints in *.

(************************************************************************************************)

Lemma lem_par_bot_to_inf_beta_bot : forall t s, par_bot U t s -> inf_beta_bot U t s.
Proof.
  pose_red_beta_bot; pose_inf_beta_bot; coinduction.
Qed.

Lemma lem_par_bot_over_step_beta :
  forall t1 t2 t3, par_bot U t1 t2 -> step_beta t2 t3 -> exists s, step_beta t1 s /\ par_bot U s t3.
Proof.
  intros t1 t2 t3 H1 H.
  revert t1 H1.
  induction H; intros.
  - inversion_clear H; subst.
    rewrite H0 in H1.
    inversion_clear H1; subst; [ unfold bot_redex in *; ycrush | idtac ].
    inversion_clear H; subst; [ unfold bot_redex in *; ycrush | idtac ].
    assert (par_bot U (x1 [0 := y0]) (t0 [0 := t2])) by eauto using lem_par_bot_subst.
    exists (x1 [0 := y0]).
    rewrite H2.
    pose lem_step_beta_redex; ycrush.
  - inversion_clear H1; subst; [ unfold bot_redex in *; ycrush | idtac ].
    generalize (IHcomp_clos x0 H2); intro; sintuition.
    exists (app s y0).
    rewrite <- H0.
    pose_term_eq; yelles 1.
  - inversion_clear H1; subst; [ unfold bot_redex in *; ycrush | idtac ].
    generalize (IHcomp_clos y0 H3); intro; sintuition.
    exists (app x0 s).
    rewrite <- H0.
    pose_term_eq; yelles 1.
  - inversion_clear H1; subst; [ unfold bot_redex in *; ycrush | idtac ].
    generalize (IHcomp_clos x0 H0); intro; sintuition.
    pose_term_eq; yelles 1.
Qed.

Lemma lem_par_bot_over_red_beta :
  forall t1 t2 t3, par_bot U t1 t2 -> red_beta t2 t3 -> exists s, red_beta t1 s /\ par_bot U s t3.
Proof.
  intros t1 t2 t3 H1 H.
  revert t1 H1.
  induction H; pose lem_par_bot_trans; pose lem_par_bot_over_step_beta; pose_red_beta; ycrush.
Qed.

Lemma lem_step_beta_bot_disj : forall t s, step_beta_bot U t s -> step_beta t s \/ step_bot U t s.
Proof.
  induction 1; sintuition; unfold beta_bot_redex in *; ycrush.
Qed.

Lemma lem_red_beta_bot_decompose : forall t s, red_beta_bot U t s -> exists r, red_beta t r /\ par_bot U r s.
Proof.
  intros t s H.
  induction H.
  - pose lem_par_bot_refl; pose_red_beta; ycrush.
  - assert (HH: step_beta x y \/ step_bot U x y) by eauto using lem_step_beta_bot_disj.
    destruct HH;
      pose lem_step_bot_to_par_bot; pose lem_par_bot_trans; pose lem_par_bot_over_red_beta;
        pose_red_beta; ycrush.
Qed.

Corollary cor_par_bot_over_red_beta_bot :
  forall t1 t2 t3, par_bot U t1 t2 -> red_beta_bot U t2 t3 ->
                   exists s, red_beta t1 s /\ par_bot U s t3.
Proof.
  intros t1 t2 t3 H1 H2.
  generalize (lem_red_beta_bot_decompose t2 t3 H2).
  intro H.
  destruct H as [r H].
  destruct H as [H3 H4].
  generalize (lem_par_bot_over_red_beta t1 t2 r H1 H3).
  pose lem_par_bot_over_red_beta; pose lem_par_bot_trans; ycrush.
Qed.

Lemma lem_inf_beta_bot_prepend_par_bot :
  forall t1 t2 t3, par_bot U t1 t2 -> inf_beta_bot U t2 t3 -> inf_beta_bot U t1 t3.
Proof.
  coinduct CH on 4.
  - clear CH.
    Reconstr.rcrush (lem_par_bot_to_inf_beta_bot, lem_inf_beta_bot_prepend,
                     lem_red_beta_to_red_beta_bot, cor_par_bot_over_red_beta_bot)
                    Reconstr.Empty.
  - clear CH.
    Reconstr.rcrush (lem_par_bot_to_inf_beta_bot, cor_par_bot_over_red_beta_bot,
                     lem_inf_beta_bot_prepend_red_beta) Reconstr.Empty.
  - generalize (cor_par_bot_over_red_beta_bot t1 t2 (app x y) H H1).
    intro; simp_hyps.
    inversion H5; subst.
    + clear CH; pose_red_beta_bot; ycrush.
    + apply inf_clos_app with (x := x0) (y := y0).
      * clear CH; pose lem_red_beta_to_red_beta_bot; ycrush.
      * eapply CH; clear CH; eauto.
      * eapply CH; clear CH; eauto.
  - generalize (cor_par_bot_over_red_beta_bot t1 t2 (abs x) H H1).
    intro; simp_hyps.
    inversion H4; subst.
    + clear CH; pose_red_beta_bot; ycrush.
    + apply inf_clos_abs with (x := x0).
      * clear CH; pose lem_red_beta_to_red_beta_bot; ycrush.
      * eapply CH; clear CH; eauto.
Qed.

(************************************************************************************************)

Lemma lem_par_bot_app_choice :
  forall t s1 s2, par_bot U t (app s1 s2) -> { p : term * term | t = app (fst p) (snd p) /\
                                                                 par_bot U (fst p) s1 /\ par_bot U (snd p) s2 }.
Proof.
  intros.
  apply constructive_indefinite_description.
  generalize (lem_par_bot_app t s1 s2 H); intro; sintuition.
  exists (t1, t2).
  ycrush.
Qed.

Lemma lem_par_bot_abs_choice :
  forall t y, par_bot U t (abs y) -> { x | t = abs x /\ par_bot U x y }.
Proof.
  intros.
  apply constructive_indefinite_description.
  apply lem_par_bot_abs.
  assumption.
Qed.

Lemma lem_red_beta_bot_decompose_choice :
  forall t s, red_beta_bot U t s -> { r | red_beta t r /\ par_bot U r s }.
Proof.
  intros.
  apply constructive_indefinite_description.
  apply lem_red_beta_bot_decompose.
  assumption.
Qed.

(************************************************************************************************)

CoFixpoint F_inf_beta_bot_decompose (t s : term) (p : inf_beta_bot U t s) : term.
destruct (lem_inf_clos_cases t s p).
- destruct (lem_red_beta_bot_decompose_choice t bot r).
  exact x.
- destruct (lem_red_beta_bot_decompose_choice t (var n) r).
  exact x.
- destruct (lem_red_beta_bot_decompose_choice t (app x y) r).
  destruct a.
  destruct (lem_par_bot_app_choice x0 x y H0).
  destruct a.
  assert (HH1: inf_beta_bot U (fst x1) x') by (pose lem_inf_beta_bot_prepend_par_bot; ycrush).
  assert (HH2: inf_beta_bot U (snd x1) y') by (pose lem_inf_beta_bot_prepend_par_bot; ycrush).
  exact (app (F_inf_beta_bot_decompose (fst x1) x' HH1) (F_inf_beta_bot_decompose (snd x1) y' HH2)).
- destruct (lem_red_beta_bot_decompose_choice t (abs x) r).
  destruct a.
  destruct (lem_par_bot_abs_choice x0 x H0).
  destruct a.
  assert (HH: inf_beta_bot U x1 x') by (pose lem_inf_beta_bot_prepend_par_bot; ycrush).
  exact (abs (F_inf_beta_bot_decompose x1 x' HH)).
Defined.

Theorem thm_inf_beta_bot_decompose :
  forall t s, inf_beta_bot U t s -> exists r, inf_beta t r /\ par_bot U r s.
Proof.
  enough (exists f, forall t s (p : inf_beta_bot U t s),
               inf_beta t (f t s p) /\ par_bot U (f t s p) s) by ycrush.
  exists F_inf_beta_bot_decompose.
  split.
  - revert t s p.
    cofix CH.
    intros t s p.
    peek (F_inf_beta_bot_decompose t s p).
    destruct (lem_inf_clos_cases t s p).
    + clear CH; destruct (lem_red_beta_bot_decompose_choice t _ r); pose_inf_beta; ycrush.
    + clear CH; destruct (lem_red_beta_bot_decompose_choice t _ r); pose_inf_beta; ycrush.
    + destruct (lem_red_beta_bot_decompose_choice t (app x y) r).
      destruct a; simpl.
      destruct (lem_par_bot_app_choice x0 x y p0).
      destruct a; simpl.
      apply inf_clos_app with (x := fst x1) (y := snd x1).
      * clear CH; pose_red_beta_bot; ycrush.
      * eapply CH; clear CH; eauto.
      * eapply CH; clear CH; eauto.
    + destruct (lem_red_beta_bot_decompose_choice t (abs x) r).
      destruct a; simpl.
      destruct (lem_par_bot_abs_choice x0 x p0).
      destruct a; simpl.
      apply inf_clos_abs with (x := x1).
      * clear CH; pose_red_beta_bot; ycrush.
      * eapply CH; clear CH; eauto.
  - revert t s p.
    cofix CH.
    intros t s p.
    peek (F_inf_beta_bot_decompose t s p).
    destruct (lem_inf_clos_cases t s p).
    + clear CH; destruct (lem_red_beta_bot_decompose_choice t _ r); ycrush.
    + clear CH; destruct (lem_red_beta_bot_decompose_choice t _ r); ycrush.
    + destruct (lem_red_beta_bot_decompose_choice t (app x y) r).
      destruct a; simpl.
      destruct (lem_par_bot_app_choice x0 x y p0).
      destruct a; simpl.
      apply par_clos_app.
      * eapply CH.
      * eapply CH.
    + destruct (lem_red_beta_bot_decompose_choice t (abs x) r).
      destruct a; simpl.
      destruct (lem_par_bot_abs_choice x0 x p0).
      destruct a; simpl.
      apply par_clos_abs.
      eapply CH.
Qed.

End Botred.

(************************************************************************************************)

Section Botred_strong.

Variable U : term -> Prop.
Variable Hs : strongly_meaningless U.

Corollary cor_inf_beta_bot_preserves_U_rev : forall t s, U s -> inf_beta_bot U t s -> U t.
Proof.
  destruct Hs as [Hm He].
  intros t s Hu H.
  generalize (thm_inf_beta_bot_decompose U Hm t s H).
  intros; sintuition.
  assert (U r) by (apply lem_par_bot_preserves_U_rev with (t := s); assumption).
  ycrush.
Qed.

Lemma lem_inf_beta_bot_to_bot_redex :
  forall t s u, inf_beta_bot U t s -> bot_redex U s u -> inf_beta_bot U t u.
Proof.
  destruct Hs as [Hm He].
  unfold bot_redex.
  intros.
  assert (U t) by (pose cor_inf_beta_bot_preserves_U_rev; ycrush).
  apply lem_red_beta_bot_to_inf_beta_bot; auto.
  pose lem_red_beta_bot_redex_U; ycrush.
Qed.

Lemma lem_inf_beta_bot_append_par_bot :
  forall t t' s, inf_beta_bot U t t' -> par_bot U t' s -> inf_beta_bot U t s.
Proof.
  destruct Hs as [Hm He].
  coinduct CH.
  - clear CH; destruct s; sauto.
  - clear CH; destruct s.
    + intro H1; inversion H1; subst; eapply lem_inf_beta_bot_to_bot_redex; eauto.
    + intro H1; inversion H1; subst; [ unfold bot_redex in *; ycrush | assumption ].
    + sauto.
    + sauto.
  - csolve CH using eauto.
    clear CH; eapply lem_inf_beta_bot_to_bot_redex; eauto.
  - csolve CH using eauto.
    clear CH; eapply lem_inf_beta_bot_to_bot_redex; eauto.
Qed.

Corollary cor_inf_beta_bot_append_red_beta :
  forall t s r, inf_beta_bot U t s -> red_beta s r -> inf_beta_bot U t r.
Proof.
  destruct Hs as [Hm He].
  intros t s r H1 H2.
  generalize (thm_inf_beta_bot_decompose U Hm t s H1); intro HH.
  destruct HH as [ t' [ H3 H4 ]].
  generalize (lem_par_bot_over_red_beta U Hm t' s r H4 H2); intro HH.
  destruct HH as [ s' [ H5 H6 ]].
  assert (inf_beta_bot U t s') by (apply lem_inf_beta_to_inf_beta_bot; pose_inf_beta; ycrush).
  eapply lem_inf_beta_bot_append_par_bot; eauto.
Qed.

End Botred_strong.

Ltac pose_red_beta_bot :=
  pose proof lem_red_beta_bot_refl_0; pose proof lem_red_beta_bot_refl; pose proof lem_red_beta_bot_trans;
  pose proof lem_red_beta_bot_step; pose proof lem_red_beta_bot_step_rev;
  pose proof lem_red_beta_bot_redex_beta; pose proof lem_red_beta_bot_redex_bot;
  pose proof lem_step_beta_bot_to_red_beta_bot; pose proof lem_red_beta_to_red_beta_bot;
  pose proof lem_step_beta_to_red_beta_bot; pose proof lem_step_beta_to_step_beta_bot;
  pose proof lem_red_beta_bot_app; pose proof lem_red_beta_bot_abs;
  pose proof lem_red_beta_bot_redex_U;
  autounfold with shints in *.

Ltac pose_inf_beta_bot := pose proof lem_inf_beta_bot_refl; pose proof lem_inf_beta_to_inf_beta_bot;
                          pose proof lem_red_beta_bot_to_inf_beta_bot; pose proof lem_inf_beta_bot_prepend;
                          pose proof lem_inf_beta_bot_prepend_red_beta;
                          pose proof lem_inf_beta_bot_app; pose proof lem_inf_beta_bot_abs;
                          autounfold with shints in *.
