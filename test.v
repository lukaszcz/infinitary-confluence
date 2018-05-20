
Require Import Arith.Even.
Require Import Omega.

Inductive evenS : nat -> Set :=
| evenS_0 : evenS 0
| evenS_S : forall n, evenS n -> evenS (S (S n)).

Lemma lem_eqv : forall k n, n <= k -> even n -> exists p : evenS n, True.
Proof.
  induction k; intros n H H1.
  - assert (HH: n = 0) by omega.
    rewrite HH.
    exists evenS_0.
    auto.
  - inversion H1.
    + exists evenS_0; auto.
    + inversion H0.
      assert (n1 <= k) by omega.
      generalize (IHk n1 H5 H3); intro HH.
      destruct HH.
      exists (evenS_S n1 x).
      auto.
Qed.

Lemma lem_eqv_1 : forall k n, n <= k -> evenS n -> even n.
Proof.
  induction k; intros n H H1.
  - assert (HH: n = 0) by omega.
    rewrite HH.
    apply even_O.
  - inversion H1.
    + apply even_O.
    + apply even_S.
      apply odd_S.
      apply IHk; [ omega | trivial ].
Qed.

Lemma lem_prop : forall A B, A \/ B -> exists p : {A}+{B}, True.
Proof.
  intros.
  destruct H.
  - exists (left H); trivial.
  - exists (right H); trivial.
Qed.

Require Import Logic.IndefiniteDescription.

Definition fun_eqv : forall n, even n -> evenS n.
  intros.
  assert (n <= n) by omega.
  generalize (lem_eqv n n H0 H); intro.
  generalize (constructive_indefinite_description (fun _ : evenS n => True) H1); intro.
  elim H2.
  auto.
Defined.

Definition def_prop : forall A B, A \/ B -> {A}+{B}.
  intros.
  generalize (lem_prop A B H); intro H1.
  generalize (constructive_indefinite_description (fun _ : {A}+{B} => True) H1); intro H2.
  elim H2.
  auto.
Defined.
