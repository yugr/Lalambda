Theorem mul_0_r :
  forall (n : nat), n * 0 = 0.
intros.
induction n as [| n' IHn'].
- reflexivity.
- simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem plus_n_Sm :
  forall (n m : nat), S (n + m) = n + S m.
intros.
induction n as [|n' IHn'].
- simpl.
  reflexivity.
- simpl.  (* TODO: what happened here?! *)
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem plus_n_0 :
  forall (n : nat), n + 0 = n.
intros.
induction n as [|n' IHn'].
- unfold "+".
  reflexivity.
- simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Lemma plus_S :
  forall (m n : nat), S (m + n) = m + S n.
intros.
induction m as [|n' IHn'].
- simpl.
  reflexivity.
- simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Theorem add_comm :
  forall (n m : nat), n + m = m + n.
intros.
induction n as [|n' IHn'].
- simpl.
  rewrite -> plus_n_0.
  reflexivity.
- simpl.
  rewrite IHn'.
  rewrite <- plus_S.
  reflexivity.
Qed.

Theorem add_assoc :
  forall (n m p : nat),
  (n + m) + p = n + (m + p).
intros.
induction n as [|n' IHn'].
- simpl.
  reflexivity.
- simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall (n : nat), double n = n + n.
intros.
induction n as [|n' IHn'].
- (* n = 0 *)
  reflexivity.
- (* n = S n' *)
  simpl.
  rewrite IHn'.
  rewrite -> plus_S.
  reflexivity.
Qed.

Fixpoint even (n : nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => even n'
  end.

Theorem even_S :
  forall (n : nat), even (S n) = negb (even n).
intros.
induction n as [|n' IHn'].
- simpl.
  reflexivity.
Admitted.

(*
Theorem: For any natural n and m,
  n + m = m + n.
Proof: By unduction on n.
* First suppose n = 0. We must show that
    0 + m = m + 0.
This follows directly from definition of + (?!).
* Next, suppose n = S n' and
  n' + m = m + n'.
We must show that
  S n' + m = m + S n'.
Following definition of +, we can rewrite LHS as
  S (n' + m)
which, according to inductive hypothesis, is the same as
  S (m + n')
which, as prooved in preceeding lemma, can be rewritten as
  m + S n'.
We thus have a trivial equality.
Qed.
*)

Theorem add_shuffle3 :
  forall (n m p : nat), n + (m + p) = m + (n + p).
Proof.
intros.
assert (n + (m + p) = (m + p) + n) as H.
- rewrite add_comm.
  reflexivity.
- rewrite H.
  rewrite add_assoc.
  assert (H1: n + p = p + n).
  + rewrite add_comm. reflexivity.
  + rewrite H1. reflexivity.
Qed.

Lemma mult_0:
  forall (n : nat), n * 0 = 0.
Proof.
intros.
induction n as [|n' IHn'].
- reflexivity.
- simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Lemma add_0:
  forall (n : nat), n + 0 = n.
Proof.
intros.
induction n as [|n' IHn'].
- simpl.
  reflexivity.
- simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Lemma mult_S_lhs:
  forall (n m : nat), S n * m = n * m + m.
Proof.
intros.
destruct n.
- simpl.
  rewrite -> add_0.
  reflexivity.
- simpl.
  rewrite add_assoc.
  assert (H: m + n * m = n * m + m).
  + rewrite add_comm.
    reflexivity.
  + rewrite H.
    reflexivity.
Qed.

Lemma mult_S_rhs:
  forall (n m : nat), n * S m = n + n * m.
Proof.
intros.
induction n as [|n' IHn'].
- simpl.
  reflexivity.
- simpl.
  rewrite IHn'.
  rewrite add_shuffle3.
  reflexivity.
Qed.

Theorem mul_comm:
  forall (n m : nat), n * m = m * n.
Proof.
intros.
induction n as [|n' IHn'].
- simpl.
  rewrite -> mult_0.
  reflexivity.
- simpl.
  rewrite IHn'.
  rewrite mult_S_rhs.
  reflexivity.
Qed.

Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O, _       => true
  | _, O       => false
  | S n', S m' => leb n' m'
  end.

Check leb.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Theorem leb_refl :
  forall (n : nat), n <=? n = true.
Proof.
intros.
induction n as [|n' IHn'].
- simpl.
  reflexivity.
- simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O       => true
  | S n', S m' => eqb n' m'
  | _, _       => false
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem zero_negb_S :
  forall (n : nat),
  0 =? (S n) = false.
Proof.
intros.
unfold "=?".
reflexivity.
Qed.

Definition andb (a b : bool) : bool :=
  match a, b with
  | false, _ => false
  | _, false => false
  | _, _     => true
  end.

Theorem andb_false_r :
  forall (b : bool), andb b false = false.
Proof.
intros.
destruct b; unfold andb; reflexivity.
Qed.

Theorem plus_leb_compat_l :
  forall (n m p : nat), n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
intros.
induction p as [|p' IHp']; simpl; assumption.
Qed.

Theorem S_neqb_0 :
  forall (n : nat), S n =? 0 = false.
Proof.
intros.
unfold "=?".
reflexivity.
Qed.

Theorem mult_1_1 :
  forall (n : nat), 1 * n = n.
Proof.
intros.
unfold "*".
rewrite plus_n_0.
reflexivity.
Qed.

Theorem all3_spec :
  forall (b c : bool),
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
intros.
destruct c; destruct b; unfold andb; unfold negb; unfold orb; reflexivity.
Qed.

Theorem mult_plus_distr_r :
  forall (n m p : nat),
  (n + m) * p = n * p + m * p.
Proof.
intros.
induction p as [|p' IHp'].
Admitted. (* Too boring ... *)

Theorem mult_assoc :
  forall (n m p : nat), n * (m * p) = (n * m) * p.
Proof.
intros.
induction n as [|n' IHn'].
- simpl.
  reflexivity.
- rewrite mult_S_lhs.
  rewrite mult_S_lhs.
  rewrite IHn'.
  rewrite -> mult_plus_distr_r.
  reflexivity.
Qed.

Theorem eqb_refl :
  forall (n : nat), n =? n = true.
Proof.
intros.
induction n as [|n' IHn'].
- unfold "=?".
  reflexivity.
- simpl. (* TODO: what happens here ?! *)
  assumption.
Qed.

Theorem add_shuffle3' :
  forall (n m p : nat), n + (m + p) = m + (n + p).
Proof.
intros.
replace (n + (m + p)) with ((m + p) + n).
- rewrite add_assoc.
  replace (p + n) with (n + p); rewrite add_comm; reflexivity.
- rewrite add_comm.
  reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | B_0 (n : bin)
  | B_1 (n : bin).

Fixpoint incr (m : bin) : bin :=
  match m with
  | Z      => B_1 Z
  | B_0 m' => B_1 m'
  | B_1 m' => B_0 (incr m')
  end.

Fixpoint bin2nat (m : bin) : nat :=
  match m with
  | Z      => O
  | B_0 m' => 2 * bin2nat m'
  | B_1 m' => 2 * bin2nat m' + 1
  end.

Lemma plus_1_is_S :
  forall (n : nat),
  n + 1 = S n.
Proof.
intros.
rewrite add_comm.
unfold "+".
reflexivity.
Qed.

Theorem binary_commute :
  forall (b : bin), bin2nat (incr b) = S (bin2nat b).
Proof.
intros.
induction b.
- simpl.
  reflexivity.
- unfold incr.
  simpl.
  rewrite plus_1_is_S.
  reflexivity.
- simpl.
  rewrite IHb.
  simpl.
  rewrite add_0.
  replace (S (bin2nat b)) with (bin2nat b + 1).
  + rewrite add_assoc.
    reflexivity.
  + rewrite plus_1_is_S.
    reflexivity.
Qed.

(* TODO: binary inverse *)