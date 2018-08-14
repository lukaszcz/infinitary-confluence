(* This file formalises the lemmas from subsection 5.1, plus a few
   trivial properties of (sim U) left implicit in the paper text. *)

Require Import beta.
Require Import cases.

Section Sim.

Variable U : term -> Prop.

Lemma lem_U_morphism : meaningless U -> forall x y, U x -> x == y -> U y.
Proof.
  intros.
  assert (inf_beta x y) by (pose_inf_beta; ycrush).
  sauto.
Qed.

Lemma lem_sim_morphism : meaningless U -> morphism (sim U).
Proof.
  intro Hm.
  unfold morphism.
  coinduction CH.
  - clear CH; pose lem_U_morphism; ycrush.
  - destruct x'0, y'0; try solve [ clear CH; sauto ].
    intros.
    apply par_clos_app.
    + apply CH with (x := x0) (y := x'); clear CH; pose_term_eq; ycrush.
    + apply CH with (x := y0) (y := y'); clear CH; pose_term_eq; ycrush.
Qed.

Lemma lem_par_bot_to_sim :
  U bot -> forall x y, par_bot U x y -> sim U x y.
Proof.
  intro; coinduction using ssolve.
Qed.

Lemma lem_sim_refl_0 : reflexive term (sim U).
Proof.
  coinduction on 0.
Qed.

Lemma lem_sim_refl :
  (forall x y, U x -> x == y -> U y) -> forall x y, x == y -> sim U x y.
Proof.
  intro; coinduction.
Qed.

Lemma lem_sim_sym : symmetric term (sim U).
Proof.
  coinduction.
Qed.

(* Lemma 5.4 *)
Lemma lem_sim_trans : meaningless U -> transitive term (sim U).
Proof.
  unfold meaningless.
  intro H; simp_hyps.
  coinduction CH using auto.
  - csolve CH.
  - cintro; [ pose lem_sim_sym; clear CH; constructor; sintuition; eauto |
              constructor 4; eapply CH; eauto ].
  - cintro; [ pose lem_sim_sym; clear CH; constructor; sintuition; eauto |
              constructor 5; eapply CH; eauto ].
Qed.

Lemma lem_sim_subset (R : term -> Prop) : (forall x, U x -> R x) -> forall x y, sim U x y -> sim R x y.
Proof.
  intro H; coinduction.
Qed.

Lemma lem_sim_shift_closed : meaningless U -> shift_closed (sim U).
Proof.
  unfold shift_closed.
  intro H.
  coinduction.
Qed.

(* Lemma 5.1 *)
Lemma lem_sim_subst : meaningless U ->
                      forall n t t' s s', sim U t t' -> sim U s s' -> sim U (t [n := s]) (t' [n := s']).
Proof.
  intro H.
  pose lem_sim_shift_closed; coinduction.
Qed.

CoFixpoint F_sim_to_par_bot (t s : term) (p : sim U t s) : term.
destruct (lem_par_clos_cases t s p).
- exact bot.
- exact bot.
- exact (var n).
- exact (app (F_sim_to_par_bot x x' p0) (F_sim_to_par_bot y y' p1)).
- exact (abs (F_sim_to_par_bot x y p0)).
Defined.

(* Lemma 5.5 *)
Lemma lem_sim_to_par_bot : forall t s, sim U t s -> exists r, par_bot U t r /\ par_bot U s r.
Proof.
  enough (exists f, forall t s (p : sim U t s), par_bot U t (f t s p) /\ par_bot U s (f t s p)) by ycrush.
  exists F_sim_to_par_bot.
  split; revert t s p.
  - cofix CH.
    intros t s p.
    peek (F_sim_to_par_bot t s p).
    destruct (lem_par_clos_cases t s p).
    + clear CH; destruct x; sauto; constructor; constructor; pose_term_eq; ycrush.
    + clear CH; solve [ constructor ].
    + clear CH; solve [ constructor ].
    + apply par_clos_app; apply CH.
    + apply par_clos_abs; apply CH.
  - cofix CH.
    intros t s p.
    peek (F_sim_to_par_bot t s p).
    destruct (lem_par_clos_cases t s p).
    + clear CH; destruct y; sauto; constructor; constructor; pose_term_eq; ycrush.
    + clear CH; solve [ constructor ].
    + clear CH; solve [ constructor ].
    + apply par_clos_app; apply CH.
    + apply par_clos_abs; apply CH.
Qed.

(* Lemma 5.2 *)
Lemma lem_step_beta_preserves_sim : meaningless U ->
  forall t t' s, step_beta t s -> sim U t t' -> exists s', step_beta_eq t' s' /\ sim U s s'.
Proof.
  intros Hm t t' s H; revert t'.
  induction H.
  - inversion_clear H.
    intros t' H.
    inversion H; subst; clear H; try yelles 1.
    + exists t'; split.
      * pose_term_eq; ycrush.
      * assert (inf_beta x y) by
            (rewrite H0; rewrite H1; pose lem_red_beta_redex; pose_inf_beta; ycrush).
        ycrush.
    + inversion H0; subst; yisolve; fold term_eq in *.
      inversion H2; subst; try yelles 1.
      * assert (U (abs t1)) by (pose lem_U_morphism; pose_term_eq; ycrush).
        assert (U (app (abs t1) t2)) by ycrush.
        exists (app x' y'); split.
        ** pose_term_eq; ycrush.
        ** assert (sim U (app x0 y0) (app x' y')) by ycrush.
           assert (sim U (app (abs t1) t2) (app x' y')) by
               (pose lem_sim_morphism; pose_term_eq; ycrush).
           assert (inf_beta (app (abs t1) t2) y) by
            (rewrite H1; pose lem_red_beta_redex; pose_inf_beta; ycrush).
           ycrush.
      * inversion H6; subst; yisolve; fold term_eq in *.
        exists (y1 [0 := y']).
        split.
        ** pose lem_step_beta_redex; ycrush.
        ** assert (sim U (x [0 := y0]) (y1 [0 := y'])) by
              (pose lem_sim_subst; ycrush).
           assert (y == x [0 := y0]) by
               (rewrite H7; rewrite H8; assumption).
           pose lem_sim_morphism; pose_term_eq; ycrush.
  - intros t' H1.
    inversion H1; subst.
    + exists t'; split.
      * pose_term_eq; ycrush.
      * assert (inf_beta (app x y) (app x' y')) by
            (rewrite H0; pose lem_red_beta_redex; pose_inf_beta; ycrush).
        ycrush.
    + generalize (IHcomp_clos x'0 H4); intro HH; destruct HH as [s' [HH1 HH2]].
      exists (app s' y'0).
      split.
      * destruct HH1.
        ** left; constructor 2; ycrush.
        ** right; pose_term_eq; ycrush.
      * constructor 4; pose lem_sim_morphism; pose_term_eq; unfold morphism, sim in *; ycrush.
  - intros t' H1.
    inversion H1; subst.
    + exists t'; split.
      * pose_term_eq; ycrush.
      * assert (inf_beta (app x y) (app x' y')) by
            (rewrite H0; pose lem_red_beta_redex; pose_inf_beta; ycrush).
        ycrush.
    + generalize (IHcomp_clos y'0 H6); intro HH; destruct HH as [s' [HH1 HH2]].
      exists (app x'0 s').
      split.
      * destruct HH1.
        ** left; constructor 3; ycrush.
        ** right; pose_term_eq; ycrush.
      * constructor 4; pose lem_sim_morphism; pose_term_eq; unfold morphism, sim in *; ycrush.
  - intros t' H1.
    inversion H1; subst.
    + exists t'; split.
      * pose_term_eq; ycrush.
      * assert (inf_beta (abs x) (abs y)) by
            (pose lem_red_beta_redex; pose_inf_beta; ycrush).
        ycrush.
    + generalize (IHcomp_clos y0 H2); intro HH; destruct HH as [s' [HH1 HH2]].
      exists (abs s').
      split.
      * destruct HH1.
        ** left; constructor 4; ycrush.
        ** right; pose_term_eq; ycrush.
      * constructor 5; pose lem_sim_morphism; pose_term_eq; unfold morphism, sim in *; ycrush.
Qed.

Lemma lem_red_beta_preserves_sim : meaningless U ->
  forall t t' s, red_beta t s -> sim U t t' -> exists s', red_beta t' s' /\ sim U s s'.
Proof.
  intros Hm t t' s H; revert t'.
  induction H.
  - pose lem_sim_morphism; pose_term_eq; ycrush.
  - intros.
    generalize (lem_step_beta_preserves_sim Hm x t' y H H1); intro HH; destruct HH as [s [HH1 HH2]].
    generalize (IHstar s HH2); intro Hs; destruct Hs as [s0 [Hs1 Hs2]].
    exists s0.
    destruct HH1; pose_red_beta; pose_term_eq; ycrush.
Qed.

Lemma lem_red_beta_preserves_sim_choice :
  meaningless U ->
  forall t t' s, red_beta t s -> sim U t t' -> { s' | red_beta t' s' /\ sim U s s' }.
Proof.
  intros.
  apply constructive_indefinite_description.
  eapply lem_red_beta_preserves_sim; eauto.
Qed.

Lemma lem_inf_beta_preserves_sim_cases :
  meaningless U ->
  forall t t' s, inf_beta t s -> sim U t t' ->
                 red_beta t s \/
                 (exists u, red_beta t' u /\ sim U s u) \/
                 (exists s1 s2 t1 t2 u1 u2, s = app s1 s2 /\ red_beta t (app t1 t2) /\
                                            inf_beta t1 s1 /\ inf_beta t2 s2 /\
                                            sim U t1 u1 /\ sim U t2 u2 /\ red_beta t' (app u1 u2)) \/
                 (exists s0 t0 u0, s = abs s0 /\ red_beta t (abs t0) /\ inf_beta t0 s0 /\
                                   sim U t0 u0 /\ red_beta t' (abs u0)).
Proof.
  intros.
  inversion H0; subst; yisolve.
  - assert (HH: exists u, sim U (app x y) u /\ red_beta t' u) by
        Reconstr.rcrush (@beta.lem_step_beta_to_red_beta, @beta.lem_red_beta_refl, @Sim.lem_red_beta_preserves_sim, @beta.lem_red_beta_step) (@beta.step_beta_eq).
    destruct HH as [u [HH1 HH2]].
    inversion HH1; subst.
    + right; left.
      exists u.
      assert (inf_beta (app x y) (app x' y')) by
          Reconstr.reasy (@beta.lem_inf_beta_app) (@defs.inf_beta, @defs.red_beta).
      assert (U (app x' y')) by ycrush.
      ycrush.
    + right; right; left.
      exists x', y', x, y, x'0, y'0.
      ycrush.
  - assert (HH: exists u, sim U (abs x) u /\ red_beta t' u) by
        Reconstr.rcrush (@beta.lem_step_beta_to_red_beta, @beta.lem_red_beta_refl, @Sim.lem_red_beta_preserves_sim, @beta.lem_red_beta_step) (@beta.step_beta_eq).
    destruct HH as [u [HH1 HH2]].
    inversion HH1; subst.
    + right; left.
      exists u.
      assert (inf_beta (abs x) (abs x')) by
          Reconstr.reasy (@beta.lem_inf_beta_abs) (@defs.inf_beta, @defs.red_beta).
      assert (U (abs x')) by ycrush.
      ycrush.
    + right; right; right.
      exists x', x, y.
      ycrush.
Qed.

Inductive ctr (t t' s : term) : Set :=
| ctr_red : red_beta t s -> ctr t t' s
| ctr_u : forall u, red_beta t' u -> sim U s u -> ctr t t' s
| ctr_app : forall s1 s2 t1 t2 u1 u2, s = app s1 s2 -> red_beta t (app t1 t2) ->
                                      inf_beta t1 s1 -> inf_beta t2 s2 ->
                                      sim U t1 u1 -> sim U t2 u2 -> red_beta t' (app u1 u2) ->
                                      ctr t t' s
| ctr_abs : forall s0 t0 u0, s = abs s0 -> red_beta t (abs t0) -> inf_beta t0 s0 ->
                             sim U t0 u0 -> red_beta t' (abs u0) -> ctr t t' s.

Lemma lem_inf_beta_preserves_sim_cases_choice :
  meaningless U ->
  forall t t' s, inf_beta t s -> sim U t t' -> ctr t t' s.
Proof.
  intros Hm t t' s H1 H2.
  enough ({ c : ctr t t' s | True }) by ycrush.
  enough (exists c : ctr t t' s, True) by (apply constructive_indefinite_description; assumption).
  generalize (lem_inf_beta_preserves_sim_cases Hm t t' s H1 H2).
  ycrush.
Qed.

CoFixpoint F_inf_beta_preserves_sim (t t' s : term) (pu : meaningless U)
           (p1 : inf_beta t s) (p2 : sim U t t') : term.
destruct (lem_inf_beta_preserves_sim_cases_choice pu t t' s p1 p2).
- exact (proj1_sig (lem_red_beta_preserves_sim_choice pu t t' s r p2)).
- exact u.
- exact (app (F_inf_beta_preserves_sim t1 u1 s1 pu i s0) (F_inf_beta_preserves_sim t2 u2 s2 pu i0 s3)).
- exact (abs (F_inf_beta_preserves_sim t0 u0 s0 pu i s1)).
Defined.

(* Lemma 5.3 *)
Lemma lem_inf_beta_preserves_sim : meaningless U ->
  forall t t' s, inf_beta t s -> sim U t t' -> exists s', inf_beta t' s' /\ sim U s s'.
Proof.
  intro Hm.
  enough (exists f, forall t t' s (p1 : inf_beta t s) (p2 : sim U t t'),
               inf_beta t' (f t t' s Hm p1 p2) /\ sim U s (f t t' s Hm p1 p2)) by ycrush.
  exists F_inf_beta_preserves_sim.
  split.
  - revert t t' s p1 p2.
    cofix CH.
    intros.
    peek (F_inf_beta_preserves_sim t t' s Hm p1 p2).
    destruct (lem_inf_beta_preserves_sim_cases_choice Hm t t' s p1 p2).
    + clear CH; destruct (lem_red_beta_preserves_sim_choice Hm t t' _ r p2); pose_inf_beta; ycrush.
    + clear CH; pose_inf_beta; ycrush.
    + apply inf_clos_app with (x := u1) (y := u2).
      * assumption.
      * apply CH.
      * apply CH.
    + apply inf_clos_abs with (x := u0).
      * assumption.
      * apply CH.
  - revert t t' s p1 p2.
    cofix CH.
    intros.
    peek (F_inf_beta_preserves_sim t t' s Hm p1 p2).
    destruct (lem_inf_beta_preserves_sim_cases_choice Hm t t' s p1 p2).
    + clear CH; destruct (lem_red_beta_preserves_sim_choice Hm t t' _ r p2); ycrush.
    + clear CH; ycrush.
    + rewrite e.
      apply par_clos_app.
      * apply CH.
      * apply CH.
    + rewrite e.
      apply par_clos_abs.
      apply CH.
Qed.

End Sim.

Ltac pose_sim := pose proof lem_par_bot_to_sim; pose proof lem_sim_refl_0;
                 pose proof lem_sim_refl; pose proof lem_sim_sym; pose proof lem_sim_trans;
                 pose lem_sim_subst; pose lem_sim_to_par_bot;
                 autounfold with shints in *.
