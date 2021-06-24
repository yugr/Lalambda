Fixpoint even (n : nat) : bool :=
  match n with
  | O        => true
  | S (S n') => even n'
  | _        => false
  end.

Definition notb (b : bool) : bool :=
  if b then false else true.

Definition odd (n : nat) : bool := notb (even n).

Fixpoint add (n m : nat) : nat :=
  match n with
  | O    => m
  | S n' => add n' (S m)
  end.

Theorem silly_ex :
  forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
intros.
apply H0.
apply H.
assumption.
Qed.

Theorem silly3 :
  forall (n m : nat), n = m -> m = n.
Proof.
intros.
symmetry.
assumption.
Qed.

Definition minustwo (n : nat) : nat :=
  match n with
  | S (S n') => n'
  | _        => O
  end.

Example trans_eq_exercise :
  forall (n m o p : nat),
  m = minustwo o ->
  n + p = m ->
  n + p = minustwo o.
Proof.
intros.
rewrite H0.
assumption.
Qed.

Notation "x :: y" := (cons x y).

Example injection_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
intros.
rewrite H0 in H.
injection H as H1 H2.
rewrite <- H2 in H1.
assumption.
Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = nil ->
  x = z.
Proof.
intros.
discriminate H.
Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O       => true
  | S n', S m' => eqb n' m'
  | _, _       => false
  end.

Notation "x =? y" := (eqb x y) (at level 60).

Theorem eqb_true : forall (n m : nat), n =? m = true -> n = m.
Proof.
intros n.
induction n.
- intros.
  destruct m.
  + reflexivity.
  + simpl in H.
    discriminate H.
- intros.
  destruct m.
  + simpl in H.
    discriminate H.
  + simpl in H.
    apply IHn in H.
    rewrite H.
    reflexivity.
Qed.

Theorem plus_comm : forall (n m : nat), n + m = m + n.
Proof.
Admitted. (* Prooved before *)

Theorem plus_n_n_injective :
  forall (n m : nat), n + n = m + m -> n = m.
Proof.
intros n.
induction n.
- intros m.
  simpl.
  destruct m.
  + simpl.
    reflexivity.
  + simpl.
    intros.
    discriminate.
- simpl.
  intros.
  rewrite plus_comm in H.
  simpl in H.
  destruct m.
  + simpl in H.
    discriminate H.
  + simpl in H.
    assert (m + S m = S m + m). { apply plus_comm. }
    rewrite H0 in H.
    simpl in H.
    injection H.
    intros.
    apply IHn in H1.
    rewrite H1.
    reflexivity.
Qed.

(* nth_error_after_last already prooved before *)

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | nil          => (nil, nil)
  | (x, y) :: l' =>
    match split l' with
    | (lx', ly') => (x :: lx', y :: ly')
    end
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | nil, _              => nil
  | _, nil              => nil
  | x :: lx', y :: ly' => (x, y) :: combine lx' ly'
  end.

Lemma split_nil :
  forall X Y (l : list (X *Y)) l2,
  split l = (nil, l2) -> l = nil.
Proof.
intros X Y l.
induction l.
- intros.
  reflexivity.
- intros.
  destruct a.
  simpl in H.
  destruct (split l).
  discriminate H.
Qed.

Theorem combine_split :
  forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
intros x y l.
induction l.
- intros.
  simpl in H.
  symmetry in H.
  injection H.
  intros.
  rewrite H0.
  rewrite H1.
  simpl.
  reflexivity.
- intros.
  destruct a.
  simpl in H.
  destruct (split l).
  injection H.
  intros.
  rewrite <- H0.
  rewrite <- H1.
  simpl.
  assert (combine l0 l3 = l). {apply IHl. reflexivity. }
  rewrite H2.
  reflexivity.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
intros.
destruct b.
- destruct (f true) eqn:Htrue.
  + rewrite Htrue.
    assumption.
  + destruct (f false) eqn:Hfalse.
    ++ assumption.
    ++ assumption.
- destruct (f false) eqn:Hfalse.
  + destruct (f true) eqn:Htrue.
    ++ assumption.
    ++ assumption.
  + rewrite Hfalse.
    assumption.
Qed.