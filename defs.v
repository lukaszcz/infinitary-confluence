
Require Export Arith.
Require Export Relations.

CoInductive term : Set :=
| bot : term
| var : nat -> term
| app : term -> term -> term
| abs : term -> term.

CoInductive par_clos (R : relation term) : relation term :=
| par_clos_base : forall x y, R x y -> par_clos R x y
| par_clos_bot : par_clos R bot bot
| par_clos_var : forall n, par_clos R (var n) (var n)
| par_clos_app : forall x y x' y', par_clos R x x' -> par_clos R y y' -> par_clos R (app x y) (app x' y')
| par_clos_abs : forall x y, par_clos R x y -> par_clos R (abs x) (abs y).

(* equality (identity) of infinitary terms *)
Definition term_eq := par_clos (fun _ _ => False).

Notation "A == B" := (term_eq A B) (at level 70).
Notation "A != B" := (~(term_eq A B)) (at level 70).

Definition morphism (R : relation term) := forall x y, R x y -> forall x' y', x == x' -> y == y' -> R x' y'.

CoFixpoint shift d c t : term :=
  match t with
    | bot => bot
    | var n => var (if c <=? n then n + d else n)
    | app t1 t2 => app (shift d c t1) (shift d c t2)
    | abs t1 => abs (shift d (c+1) t1)
  end.

Definition shift_closed (R : relation term) :=
  forall d c t t', R t t' -> R (shift d c t) (shift d c t').

CoFixpoint subst n s t : term :=
  match t with
  | bot => bot
  | var m => if n <? m then var (m - 1) else if n =? m then shift n 0 s else var m
  | app t1 t2 => app (subst n s t1) (subst n s t2)
  | abs t' => abs (subst (n+1) s t')
  end.

Notation "A [ N := B ]" := (subst N B A) (at level 50).

Definition subst_closed (R : relation term) :=
  forall x x' n y, R x x' -> R (x[n := y]) (x'[n := y]).

Inductive beta_redex : relation term :=
| beta_redex_c : forall x y t1 t2, x == (app (abs t1) t2) -> y == (t1[0 := t2]) ->
                                   beta_redex x y.

Inductive comp_clos (R : relation term) : relation term :=
| comp_clos_base : forall x y, R x y -> comp_clos R x y
| comp_clos_app_l : forall x y x' y', comp_clos R x x' -> y == y' -> comp_clos R (app x y) (app x' y')
| comp_clos_app_r : forall x y x' y', comp_clos R y y' -> x == x' -> comp_clos R (app x y) (app x' y')
| comp_clos_abs : forall x y, comp_clos R x y -> comp_clos R (abs x) (abs y).

(* beta reduction step *)
Definition step_beta := comp_clos beta_redex.

Inductive star (R : relation term) : relation term :=
| star_refl : forall x y, x == y -> star R x y
| star_step : forall x y z, R x y -> star R y z -> star R x z.

(* finitary beta reduction *)
Definition red_beta := star step_beta.

CoInductive inf_clos (R : relation term) : relation term :=
| inf_clos_bot : forall s, R s bot -> inf_clos R s bot
| inf_clos_var : forall s n, R s (var n) -> inf_clos R s (var n)
| inf_clos_app : forall s x y x' y', R s (app x y) -> inf_clos R x x' -> inf_clos R y y' ->
                                     inf_clos R s (app x' y')
| inf_clos_abs : forall s x x', R s (abs x) -> inf_clos R x x' -> inf_clos R s (abs x').

Definition aux_clos (R : relation term) := inf_clos (inf_clos (star R)).

(* infinitary beta reduction *)
Definition inf_beta := inf_clos red_beta.

(* weak head reduction step *)
Inductive step_wh : relation term :=
| wh_base : forall x y, beta_redex x y -> step_wh x y
| wh_step : forall x x' y y', step_wh x x' -> y == y' -> step_wh (app x y) (app x' y').

Definition red_wh := star step_wh.
Definition inf_wh := inf_clos red_wh.

Definition is_abs t := match t with abs _ => True | _ => False end.

Definition is_rnf (t : term) :=
  match t with
  | bot => False
  | var _ => True
  | abs _ => True
  | app x y => forall z, inf_beta x z -> ~(is_abs z)
  end.

Definition has_rnf t := exists t', is_rnf t' /\ inf_beta t t'.
Definition root_active t := ~(has_rnf t).

Definition sim (U : term -> Prop) := par_clos (fun x y => U x /\ U y).

Definition meaningless (U : term -> Prop) :=
  U bot /\
  (forall x y, U x -> inf_beta x y -> U y) /\
  (forall x y n, U x -> U (x[n := y])) /\
  (forall x d c, U x -> U (shift d c x)) /\
  (forall x y, U (abs x) -> U (app (abs x) y)) /\
  (forall x, root_active x -> U x) /\
  (forall x y, U x -> sim U x y -> U y).

Definition strongly_meaningless (U : term -> Prop) :=
  meaningless U /\ forall x y, U y -> inf_beta x y -> U x.

Definition bot_redex (U : term -> Prop) (x y : term) := U x /\ x != bot /\ y == bot.
Definition beta_bot_redex U x y := beta_redex x y \/ bot_redex U x y.
Definition step_bot U := comp_clos (bot_redex U).
Definition step_beta_bot U := comp_clos (beta_bot_redex U).
Definition red_beta_bot U := star (step_beta_bot U).
Definition inf_beta_bot U := inf_clos (red_beta_bot U).
Definition par_beta_bot U := par_clos (beta_bot_redex U).
Definition par_bot U := par_clos (bot_redex U).

Definition nf (R : relation term) (t : term) := forall s, ~(R t s).
Hint Unfold nf.

Definition nf_beta := nf step_beta.
Definition nf_beta_bot U := nf (step_beta_bot U).

(************************************************************************)
(* Assumed axioms: constructive indefinite description (see cases.v)
   and some specializations of the excluded middle. *)

Axiom is_rnf_xm : forall t, is_rnf t \/ ~(is_rnf t).
Axiom has_rnf_xm : forall t, has_rnf t \/ ~(has_rnf t).
Axiom strongly_meaningless_xm : forall U, strongly_meaningless U -> forall t, U t \/ ~(U t).
