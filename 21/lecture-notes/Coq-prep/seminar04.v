From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* SSReflect tactic practice *)

Section IntLogic.

Variables A B C : Prop.

(** * Exercise *)
Lemma andA :
  (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
intros.
destruct H as [[Ha Hb] Hc].
split.
- assumption.
- split.
  + assumption.
  + assumption.
Qed.

Lemma andA' :
  (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
case.
case=> a b c.
split.
- exact: a.
- split.
  + exact: b.
  + exact: c.
Qed.

About andA.

Compute andA.

About andA'.

Compute andA'.

(** * Exercise *)
Lemma conj_disjD :
  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
intros.
destruct H as [H0 [H1 | H2]].
- left.
  split; assumption.
- right.
  split; assumption.
Qed.

Lemma conj_disjD' :
  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
case=> a.
case.
- move=> b.
  left.
  split.
  + exact: a.
  + exact: b.
- move=> c.
  right.
  split.
  + exact: a.
  + exact: c.
Qed.

Lemma conj_disjD'' :
  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
case=> [a [b | c]]; [left | right]; split; done.
Qed.

(** * Exercise *)

Lemma disj_conjD :
  A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
intros.
destruct H as [Ha | [Hb Hc]].
- split; left; assumption.
- split; right; assumption.
Qed.

Lemma disj_conjD' :
  A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
case.
- move=> a.
  split.
  + left.
    exact: a.
  + left.
    exact: a.
- case.
  move=> b c.
  split.
  + right.
    exact: b.
  + right.
    exact: c.
Qed.

Lemma disj_conjD'' :
  A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
case.
- move=> a.
  split; left; exact.
- case.
  move=> b c.
 split; right; exact.
Qed.

Lemma disj_conjD''' :
  A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
case=> [a | [b c]]; split; [left | left | right | right]; done.
Qed.

Lemma disj_conjD'''' :
  A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
case=> [a | [b c]]; split; (left + right); done.
Qed.

(** * Exercise *)
Lemma notTrue_iff_False :
  (~ True) <-> False.
Proof. 
split.
- apply.
  exact: I.
- move=> f.
  exact.
Qed.

(** Hint 1: use [case] tactic on a proof of [False] to apply the explosion
principle. *)
(** Hint 2: to solve the goal of the form [True], use [exact: I], or simple
automation. *)


(** * Exercise *)

Lemma imp_trans :
  (A -> B) -> (B -> C) -> (A -> C).
Proof.
move=> ab bc a.
apply: bc.
apply: ab.
done.
Qed.

(** * Exercise *)
Lemma dne_False :
  ~ ~ False -> False.
Proof.
unfold not.
apply.
apply.
Qed.

(** * Exercise *)
Lemma dne_True :
  ~ ~ True -> True.
Proof.
unfold not.
move=> lhs.
exact: I.
Qed.

(** * Exercise *)
Lemma DNE_triple_neg :
  ~ ~ ~ A -> ~ A.
Proof.
unfold not.
intros.
apply H.
intros.
apply H1.
assumption.
Qed.

Lemma DNE_triple_neg' :
  ~ ~ ~ A -> ~ A.
Proof.
unfold not.
move=> triple_neg a.
apply: triple_neg.
apply.
exact: a.
Qed.

(** Hint : use `apply: (identifier)`
to apply a hypothesis from the context to
the goal and keep the hypothesis in the context *)

End IntLogic.

(*Lemma split_assumptions (P Q R : Prop):
  (P \/ Q -> R) -> ((P -> R) \/ (Q ->R)).
Proof.
move=> H.*)

(** * Exercise *)
Lemma nlem' (A : Prop):
  ~ (A \/ ~ A) -> A.
Proof.
move=> H.
have: ~ A /\ ~ ~ A.
- admit. (* TODO *)
case=> [na nna].
rewrite /not in na nna.
move: (nna na).
case.
Admitted.

(** Hint: you might want to use a separate lemma here to make progress.
Or, use the `have` tactic: `have: statement` creates a new subgoal and asks
you to prove the statement. This is like a local lemma. *)


(** * Exercise *)
Lemma weak_Peirce (A B : Prop) :
  ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
Admitted.


(** * Exercise *)
(* Prove that having a general fixed-point combinator in Coq would be incosistent *)
Definition FIX := forall A : Type, (A -> A) -> A.

Lemma fix_inconsistent :
  FIX -> False.
Proof.
rewrite /FIX.
apply.
case.
Qed.

Lemma fix_inconsistent' :
  FIX -> False.
Proof.
move=> FIX.
move: (@FIX False).
apply.
apply.
Qed.

About "~~ _".

Section Boolean.
(** * Exercise *)
Lemma negbNE b : ~~ ~~ b -> b.
Proof.
unfold negb.
intros.
destruct b; assumption.
Qed.

Lemma negbNE' b : ~~ ~~ b -> b.
Proof.
rewrite /negb.
case: b; apply.
Qed.

(** * Exercise *)
Lemma negbK : involutive negb.
Proof.
rewrite /negb /involutive /cancel.
move=> x.
case: x; exact: erefl.
Qed.

Lemma esym {A : Type} (x : A) (y : A) :
  x = y -> y = x.
Proof.
move=> x_eq_y.
by rewrite x_eq_y.
Qed.

(** * Exercise *)
Lemma negb_inj : injective negb.
Proof.
rewrite /negb /injective.
move=> x1 x2.
elim x1; elim x2.
- move=> _.
  exact: erefl.
- apply esym.
- apply esym.
- move=> _.
  exact: erefl.
Qed.

End Boolean.

Section EquationalReasoning.

Variables A B : Type.

Locate "_ =1 _".
Print eqfun.

(** * Exercise 10 *)
Lemma eqext_refl (f : A -> B) :
  f =1 f.
Proof.
rewrite /eqfun.
move=> x.
exact: erefl.
(* or "by []" or "reflexivity" *)
Qed.

(** * Exercise 11 *)
Lemma eqext_sym (f g : A -> B) :
  f =1 g -> g =1 f.
Proof.
rewrite /eqfun.
move=> H.
move=> x.
rewrite (H x). (* or just "rewrite H" *)
exact: erefl.
Qed.

(** Hint: `rewrite` tactic also works with
universally quantified equalities. I.e. if you
have a hypothesis `eq` of type `forall x, f x = g
x`, you can use `rewrite eq` and Coq will usually
figure out the concrete `x` it needs to specialize
`eq` with, meaning that `rewrite eq` is
essentially `rewrite (eq t)` here. *)


(** * Exercise *)
Lemma eqext_trans (f g h : A -> B) :
  f =1 g -> g =1 h -> f =1 h.
Proof.
rewrite /eqfun.
move=> fg gh x.
rewrite (fg x).
rewrite -(gh x).
exact: erefl.
Qed.

End EquationalReasoning.



(** * Exercise *)
Lemma and_via_ex (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B.
Proof.
split.
- intros.
  destruct H.
  split.
  + assumption.
  + assumption.
- intros.
  destruct H as [a b].
  exists; assumption.
Qed.

Lemma and_via_ex' (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B.
Proof.
split.
- case=> [a b].
  by split.
- case=> [a b].
  by exists.
Qed.

(** * Exercise *)
(* Hint: the `case` tactic understands constructors are injective *)
Lemma pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2).
Proof.
intros.
inversion H.
split; reflexivity.
Qed.

(** * Exercise *)
(* Hint: the `case` tactic understands constructors are injective *)
Lemma pair_inj' A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2).
Proof.
case=> aa bb.
rewrite aa bb.
by split.
Qed.

(** * Exercise *)
Lemma false_eq_true_implies_False :
  forall n, n.+1 = 0 -> False.
Proof.
move=> n H.
discriminate H. (* or "by []" *)
Qed.

(** * Exercise *)
Lemma addn0 :
  right_id 0 addn.
Proof.
rewrite /right_id /addn.
elim.
- by [].
- move=> x IHx.
  simpl. (* or "move=> /=" *)
  rewrite IHx.
  exact: erefl.
Qed.

Locate "_ + _".
Search (_ + _).
Search "or_assoc".
About or_assoc.

(* TODO: wtf %Nrec and %coq_nat are ? *)

(** * Exercise *)

Lemma addSn :
  forall m n : nat, m.+1 + n = (m + n).+1.
Proof.
move=> m n.
move: n.
elim: m.
- move=> n.
  by [].
- move=> m IHm n.
Admitted.

Lemma addnS :
  forall m n, m + n.+1 = (m + n).+1.
Proof.
rewrite /addn.
move=> m n.
elim: m.
- by [].
- move=> m IHm.
  simpl.
  rewrite IHm.
  exact: erefl.
Qed.

Lemma addnA :
  associative addn.
Proof.
by move=> x y z; elim: x=> // x IHx; rewrite addSn IHx.
Qed.

Lemma addnC :
  commutative addn.
Proof.
elim=> [| x IHx] y; first by rewrite addn0.
by rewrite addSn IHx -addSnnS.
Qed.

(** * Exercise: *)
Lemma addnCA : left_commutative addn.
Proof.
rewrite /left_commutative.
move=> x y z.
elim: z.
- rewrite addn0.
  rewrite addn0.
  apply addnC.
- move=> n IHn.
  rewrite 100?addnS IHn.
  exact: erefl.
Qed.

(** * Exercise: *)
Lemma addnC' : commutative addn.
Proof.
rewrite /commutative.
move=> x y.
elim: x.
- rewrite addn0.

- have: 0 + x = x.
  + elim x.
    by [].
  + move=> n IHn.
    rewrite addnS IHn.
    exact: erefl.
  move=> H.
  rewrite H.
  apply addn0.
- move=> n IHn.
  
  

Admitted.


(** * Exercise (optional): *)
Lemma unit_neq_bool:
  unit <> bool.
Proof.

Admitted.

(** [==] is the decidable equality operation for types with decidable equality.
    In case of booleans it means [if and only if]. *)
    Fixpoint mostowski_equiv (a : bool) (n : nat) :=
      if n is n'.+1 then mostowski_equiv a n' == a
      else a.
    
    (** The recursive function above encodes the following classical
        propositional formula:
        [((A <-> A ...) <-> A) <-> A]
        For instance, if n equals 3 then the formula look like this
        [((A <-> A) <-> A) <-> A]
        Since we work in the classical propositional fragment
        we can encode the [<->] equivalence with boolean equality [==].
     *)
    Print odd.
    (** Try to come up with a one-line proof *)
Lemma mostowski_equiv_even_odd a n :
  mostowski_equiv a n = a || odd n.
Proof.
Admitted.

(** Write a tail-recursive variation of the [addn] function
    (let's call it [addn_iter]).
    See https://en.wikipedia.org/wiki/Tail_call
 *)

Fixpoint add_iter (n m : nat) {struct n}: nat.
  Admitted.

Lemma add_iter_correct n m :
  add_iter n m = n + m.
Proof.
Admitted.

Lemma double_inj m n :
  m + m = n + n -> m = n.
Proof.
Admitted.

Lemma nat_3k5m n : exists k m, n + 8 = 3 * k + 5 * m.
Proof. Admitted.