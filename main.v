(* This file contains our main results: subsection 5.5, subsection 5.7, corollaries 5.47, 5.48. *)

Require Import nred.
Require Import root_active.
Require Import botred.

(* Theorem 5.33 *)
Theorem thm_inf_beta_bot_confluent
        (U : term -> Prop) (Hms : strongly_meaningless U)
  : forall t t1 t2, inf_beta_bot U t t1 -> inf_beta_bot U t t2 ->
                    exists t3, inf_beta_bot U t1 t3 /\ inf_beta_bot U t2 t3.
Proof.
  destruct Hms as [Hm Hexp].
  intros.
  assert (exists t1', red_nu U Hm t1 t1') by
      (pose lem_red_nu_reduct; ycrush).
  assert (exists t2', red_nu U Hm t2 t2') by
      (pose lem_red_nu_reduct; ycrush).
  sauto.
  assert (red_nu U Hm t t1') by
      (pose lem_red_nu_inf_beta_bot_prepend; ycrush).
  assert (red_nu U Hm t t2') by
      (pose lem_red_nu_inf_beta_bot_prepend; ycrush).
  assert (t1' == t2') by
      (pose lem_red_nu_unique; ycrush).
  assert (inf_beta_bot U t1 t1') by
      (pose lem_red_nu_to_inf_beta_bot; ycrush).
  assert (inf_beta_bot U t2 t2') by
      (pose lem_red_nu_to_inf_beta_bot; ycrush).
  exists t1'.
  pose lem_inf_beta_bot_morphism; pose_term_eq; ycrush.
Qed.

Check thm_inf_beta_bot_confluent.
Print Assumptions thm_inf_beta_bot_confluent.

(* Theorem 5.34 *)
Theorem thm_inf_beta_bot_normalisation
        (U : term -> Prop) (Hms : strongly_meaningless U)
  : forall t, exists s, inf_beta_bot U t s /\ nf_beta_bot U s /\
                        forall s', inf_beta_bot U t s' -> nf_beta_bot U s' -> s' == s.
Proof.
  destruct Hms as [Hm Hexp].
  intro t.
  assert (exists s, red_nu U Hm t s) by
      (pose lem_red_nu_reduct; ycrush).
  sauto.
  assert (nf_beta_bot U s) by
      (pose lem_red_nu_nf; ycrush).
  assert (inf_beta_bot U t s) by
      (pose lem_red_nu_to_inf_beta_bot; ycrush).
  exists s.
  repeat split; try yelles 1.
  intros.
  assert (exists u, inf_beta_bot U s u /\ inf_beta_bot U s' u) by
      (pose thm_inf_beta_bot_confluent; ycrush).
  sauto.
  pose lem_inf_beta_bot_nf; pose_term_eq; ycrush.
Qed.

Check thm_inf_beta_bot_normalisation.
Print Assumptions thm_inf_beta_bot_normalisation.

(* Corollary 5.47 *)
Theorem thm_inf_beta_bot_ra_confluent
  : forall t t1 t2, inf_beta_bot root_active t t1 -> inf_beta_bot root_active t t2 ->
                    exists t3, inf_beta_bot root_active t1 t3 /\ inf_beta_bot root_active t2 t3.
Proof.
  pose thm_ra_strongly_meaningless; pose thm_inf_beta_bot_confluent; ycrush.
Qed.

Check thm_inf_beta_bot_ra_confluent.
Print Assumptions thm_inf_beta_bot_ra_confluent.

(* Corollary 5.48 *)
Theorem thm_inf_beta_bot_ra_normalisation
  : forall t, exists s, inf_beta_bot root_active t s /\ nf_beta_bot root_active s /\
                        forall s', inf_beta_bot root_active t s' -> nf_beta_bot root_active s' -> s' == s.
Proof.
  pose thm_ra_strongly_meaningless; pose thm_inf_beta_bot_normalisation; ycrush.
Qed.

Check thm_inf_beta_bot_ra_normalisation.
Print Assumptions thm_inf_beta_bot_ra_normalisation.

(* Theorem 5.49 *)
Theorem thm_inf_beta_confluent_modulo (U : term -> Prop) (Hm : meaningless U)
  : forall t t' s s', sim U t t' -> inf_beta t s -> inf_beta t' s' ->
                      exists r r', sim U r r' /\ inf_beta s r /\ inf_beta s' r'.
Proof.
  intros.
  assert (exists s0, inf_beta t s0 /\ sim U s' s0) by
      (pose lem_inf_beta_preserves_sim; pose lem_sim_sym; unfold symmetric in *; ycrush).
  simp_hyps.
  assert (inf_beta_bot root_active t s) by
      Reconstr.reasy (@botred.lem_inf_beta_to_inf_beta_bot) Reconstr.Empty.
  assert (inf_beta_bot root_active t s0) by
      Reconstr.reasy (@botred.lem_inf_beta_to_inf_beta_bot) Reconstr.Empty.
  assert (exists u, inf_beta_bot root_active s u /\ inf_beta_bot root_active s0 u) by
      Reconstr.reasy (thm_inf_beta_bot_ra_confluent) Reconstr.Empty.
  simp_hyps.
  assert (exists r, inf_beta s r /\ par_bot root_active r u) by
      Reconstr.reasy (@root_active.thm_ra_strongly_meaningless, @botred.lem_inf_beta_bot_decompose) (@defs.strongly_meaningless).
  assert (exists r0, inf_beta s0 r0 /\ par_bot root_active r0 u) by
      Reconstr.reasy (@root_active.thm_ra_strongly_meaningless, @botred.lem_inf_beta_bot_decompose) (@defs.strongly_meaningless).
  simp_hyps.
  assert (sim root_active r u) by
      Reconstr.reasy (@root_active.thm_ra_strongly_meaningless, @sim.lem_par_bot_to_sim) (@defs.meaningless, @defs.strongly_meaningless).
  assert (sim root_active r0 u) by
      Reconstr.reasy (@root_active.thm_ra_strongly_meaningless, @sim.lem_par_bot_to_sim) (@defs.meaningless, @defs.strongly_meaningless).
  assert (sim U r u) by
      (pose lem_sim_subset; ycrush).
  assert (sim U r0 u) by
      (pose lem_sim_subset; ycrush).
  assert (exists r', inf_beta s' r' /\ sim U r0 r') by
      (pose lem_inf_beta_preserves_sim; pose lem_sim_sym; unfold symmetric in *; ycrush).
  simp_hyps.
  assert (sim U r r0) by
      (eapply lem_sim_trans; pose lem_sim_sym; ycrush).
  assert (sim U r r') by
      (eapply lem_sim_trans; pose lem_sim_sym; ycrush).
  ycrush.
Qed.

Check thm_inf_beta_confluent_modulo.
Print Assumptions thm_inf_beta_confluent_modulo.
