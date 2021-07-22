Compute (orb true false).

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  if (andb b1 b2) then false else true.

Example test_nandb1 : (nandb true false) = true.
unfold nandb.
simpl.
reflexivity.
Qed.

Example test_nandb2 : (nandb false false) = true.
simpl.
reflexivity.
Qed.

Example test_nandb3 : (nandb false true) = true.
simpl.
reflexivity.
Qed.

Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
  andb b1 (andb b2 b3).

Example test_andb3 : andb3 true true true = true.
simpl.
reflexivity.
Qed.

Check andb3.

Fixpoint minus (n m : nat) :=
  match n, m with
  | O, _       => O
  | _ , O      => n
  | S n', S m' => minus n' m'
  end.

Compute minus 3 2.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O   => 1
  | S n' => n * factorial n'
  end.

Compute factorial 3.

Fixpoint ltb (n m : nat) : bool :=
  match n, m with
  | O, O       => false
  | O, _       => true
  | _, O       => false
  | S n', S m' => ltb n' m'
  end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Compute 10 <? 5.
Compute 5 <? 5.

Example test_ltb1 : (ltb 2 2) = false.
simpl.
reflexivity.
Qed.

Theorem plus_id_example : forall (n m : nat), n = m -> n + n = m + m.
intros.
rewrite -> H.
reflexivity.
Qed.

Theorem plus_id_exercise :
  forall (n m o : nat), n = m -> m = o -> n + m = m + o.
intros.
rewrite -> H.
rewrite -> H0.
reflexivity.
Qed.

Check mult_n_O.
Check mult_n_Sm.

Compute 1 * 3.

Theorem mult_n_1 : forall (p : nat), p * 1 = p.
intros.
rewrite <- mult_n_Sm.
rewrite <- mult_n_O.
reflexivity.
Qed.

Fixpoint eqb (a b : nat) :=
  match a, b with
  | O, O       => true
  | O, _       => false
  | _, O       => false
  | S a', S b' => eqb a' b'
  end.

Notation "a =? b" := (eqb a b) (at level 70) : nat_scope.

Theorem plus_1_neq_0 :
  forall (n : nat), S n =? O = false.
intros.
destruct n as [|n'] eqn:E; simpl; reflexivity.
Qed.

Theorem and_true_elim2 :
  forall (b c : bool), andb b c = true -> c = true.
intros.
destruct b.
- unfold andb in H.
  assumption.
- unfold andb in H.
  discriminate.
Qed.

Theorem zero_nbeq_plus_1 :
  forall (n : nat), 0 =? (n + 1) = false.
intros [|n']; simpl; reflexivity.
Qed.

Fail Fixpoint failing (n : nat) (b : bool) :=
  match b with
  | false => n
  | true => failing n false
  end.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
intros.
rewrite -> H.
rewrite -> H.
reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
intros.
rewrite -> H.
rewrite -> H.
destruct b; simpl; reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
intros.
destruct b.
- unfold andb in H.
  unfold orb in H.
  rewrite -> H.
  reflexivity.
- unfold andb in H.
  unfold orb in H.
  rewrite <- H.
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

Compute incr Z.
Compute incr (B_0 (B_0 Z)).
Compute incr (B_0 (B_1 Z)).
Compute incr (B_1 (B_1 Z)).

Fixpoint bin2nat_rec (m : bin) (power acc : nat) : nat :=
  match m with
  | Z      => acc
  | B_0 m' => bin2nat_rec m' (2 * power) acc
  | B_1 m' => bin2nat_rec m' (2 * power) (acc + power)
  end.

Definition bin2nat (m : bin) : nat := bin2nat_rec m 1 O.

Compute bin2nat Z.
Compute bin2nat (B_0 Z).
Compute bin2nat (B_0 (B_1 Z)).
Compute bin2nat (B_1 (B_0 (B_1 Z))).