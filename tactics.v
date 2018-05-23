
Require Export Arith.
Require Export Omega.
Require Export Relations.
Require Export Morphisms.
Require Export Setoid.

Require Export Hammer.Hammer.
Require Export Hammer.Reconstr.

Create HintDb shints discriminated.

Hint Unfold reflexive : shints.
Hint Unfold symmetric : shints.
Hint Unfold transitive : shints.

Ltac ssolve := eauto; sauto; yelles 1.

Ltac notPropAtom t :=
  lazymatch type of t with
    | Prop => tryif isAtom t then fail else idtac
    | _ => idtac
  end.

Ltac intros_until_prop_atom :=
  repeat match goal with
         | [ |- forall x : ?A, _ ] => notPropAtom A; intro
         end.

Ltac csolve0 H tac :=
  intros; autorewrite with shints;
  solve [ econstructor; solve [ eapply H; clear H; tac | try clear H; tac ] | try clear H; tac ].

Tactic Notation "cosolve" hyp(H) := csolve0 H ltac:(eauto; yelles 1).
Tactic Notation "cosolve" hyp(H) "using" tactic(tac) := csolve0 H tac.

Ltac coind_solve C tac :=
  intros_until_prop_atom;
  match goal with
  | [ |- forall _, _ ] =>
    let H := fresh "H" in
    intro H; inversion H; try subst;
    try solve [ csolve0 C tac | coind_solve C tac ]
  | _ =>
    try solve [ csolve0 C tac ]
  end.

Tactic Notation "csolve" hyp(H) := coind_solve H ltac:(eauto; yelles 1).
Tactic Notation "csolve" hyp(H) "using" tactic(tac) := coind_solve H tac.
Tactic Notation "csolve" := coind_solve 0 ltac:(eauto; yelles 1).
Tactic Notation "csolve" "using" tactic(tac) := coind_solve 0 tac.

Ltac coind_on_solve C n tac :=
  do n intro;
  match goal with
  | [ |- forall _ : ?T, _ ] =>
    isProp T;
    let H := fresh "H" in
    intro H; inversion H; try subst;
    try solve [ csolve0 C tac | coind_solve C tac ]
  | [ |- forall _ : ?T, _ ] =>
    notProp T;
    let x := fresh "x" in
    intro x; destruct x; try subst;
    try solve [ csolve0 C tac | coind_solve C tac ]
  | _ =>
    try solve [ csolve0 C tac ]
  end.

Ltac cintro := 
  match goal with
  | [ |- forall _ : ?T, _ ] =>
    isProp T;
    let H := fresh "H" in
    intro H; inversion H; try subst
  | [ |- forall _ : ?T, _ ] =>
    notProp T;
    let x := fresh "x" in
    intro x; destruct x; try subst
  end.

Tactic Notation "csolve" hyp(H) "on" int_or_var(n) := coind_on_solve H n ltac:(eauto; yelles 1).
Tactic Notation "csolve" hyp(H) "on" int_or_var(n) "using" tactic(tac) := coind_on_solve H n tac.
Tactic Notation "csolve" "on" int_or_var(n) := coind_on_solve 0 n ltac:(eauto; yelles 1).
Tactic Notation "csolve" "on" int_or_var(n) "using" tactic(tac) := coind_on_solve 0 n tac.

Tactic Notation "coinduction" ident(H) := autounfold with shints; cofix H; csolve H.
Tactic Notation "coinduction" ident(H) "using" tactic(tac) := autounfold with shints; cofix H; csolve H using tac.
Tactic Notation "coinduction" := let H := fresh "H" in coinduction H.
Tactic Notation "coinduction" "using" tactic(tac) := let H := fresh "H" in coinduction H using tac.
Tactic Notation "coinduction" ident(H) "on" int_or_var(n) := autounfold with shints; cofix H; csolve H on n.
Tactic Notation "coinduction" ident(H) "on" int_or_var(n) "using" tactic(tac) :=
  autounfold with shints; cofix H; csolve H on n using tac.
Tactic Notation "coinduction" "on" int_or_var(n) := let H := fresh "H" in coinduction H on n.
Tactic Notation "coinduction" "on" int_or_var(n) "using" tactic(tac) :=
  let H := fresh "H" in coinduction H on n using tac.

Tactic Notation "coinduct" ident(H) :=
  autounfold with shints; cofix H; intros_until_prop_atom; try cintro.
Tactic Notation "coinduct" ident(H) "on" int_or_var(n) :=
  autounfold with shints; cofix H; do n intro; try cintro.

Ltac bnat_reflect :=
  repeat match goal with
         | [ H : (?A =? ?B) = true |- _ ] =>
           notHyp (A = B);
           assert (A = B) by reasy (Arith.PeanoNat.Nat.eqb_eq) Reconstr.Empty
         | [ H : (?A =? ?B) = false |- _ ] =>
           notHyp (A <> B);
           assert (A <> B) by reasy (Arith.PeanoNat.Nat.eqb_neq) Reconstr.Empty
         | [ H : (?A <=? ?B) = true |- _ ] =>
           notHyp (A <= B);
           assert (A <= B) by reasy (Arith.Compare_dec.leb_complete) Reconstr.Empty
         | [ H : (?A <=? ?B) = false |- _ ] =>
           notHyp (B < A);
           assert (B < A) by reasy (Arith.Compare_dec.leb_complete_conv) Reconstr.Empty
         | [ H : (?A <? ?B) = true |- _ ] =>
           notHyp (A < B);
           assert (A < B) by reasy (Arith.PeanoNat.Nat.ltb_lt) Reconstr.Empty
         | [ H : (?A <? ?B) = false |- _ ] =>
           notHyp (B <= A);
           assert (B <= A) by reasy (Arith.PeanoNat.Nat.ltb_ge) Reconstr.Empty
         end; try subst; auto.

Ltac bomega := bnat_reflect; omega.
