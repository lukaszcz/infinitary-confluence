
Require Export Logic.IndefiniteDescription.

Require Import defs.
Require Import tactics.

Inductive inf_clos_cases (R : relation term) : term -> term -> Set :=
| inf_clos_cases_bot : forall t : term, R t bot -> inf_clos_cases R t bot
| inf_clos_cases_var : forall (t : term) (n : nat), R t (var n) -> inf_clos_cases R t (var n)
| inf_clos_cases_app : forall t x y x' y' : term,
    R t (app x y) -> inf_clos R x x' -> inf_clos R y y' -> inf_clos_cases R t (app x' y')
| inf_clos_cases_abs : forall t x x' : term, R t (abs x) -> inf_clos R x x' -> inf_clos_cases R t (abs x').

Lemma lem_inf_clos_cases {R : relation term} : forall t s, inf_clos R t s -> inf_clos_cases R t s.
Proof.
  enough (H: forall t s, inf_clos R t s -> { p : inf_clos_cases R t s | True }) by
      (intros t s H0; generalize (H t s H0); ycrush).
  enough (forall t s, inf_clos R t s -> exists p : inf_clos_cases R t s, True) by
      (intros; apply constructive_indefinite_description; ycrush).
  yelles 2.
Qed.

Inductive par_clos_cases (R : relation term) : term -> term -> Set :=
| par_clos_cases_base : forall x y, R x y -> par_clos_cases R x y
| par_clos_cases_bot : par_clos_cases R bot bot
| par_clos_cases_var : forall n, par_clos_cases R (var n) (var n)
| par_clos_cases_app : forall x y x' y', par_clos R x x' -> par_clos R y y' ->
                                         par_clos_cases R (app x y) (app x' y')
| par_clos_cases_abs : forall x y, par_clos R x y -> par_clos_cases R (abs x) (abs y).

Lemma lem_par_clos_cases {R : relation term} : forall t s, par_clos R t s -> par_clos_cases R t s.
Proof.
  enough (H: forall t s, par_clos R t s -> { p : par_clos_cases R t s | True }) by
      (intros t s H0; generalize (H t s H0); ycrush).
  enough (forall t s, par_clos R t s -> exists p : par_clos_cases R t s, True) by
      (intros; apply constructive_indefinite_description; ycrush).
  yelles 2.
Qed.
