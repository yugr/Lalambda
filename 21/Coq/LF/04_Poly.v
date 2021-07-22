Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check nil.

Fixpoint repeat (X : Type) (x : X) (n : nat) : list X :=
  match n with
  | O    => nil X
  | S n' => cons X x (repeat X x n')
  end.

Compute repeat nat 2 2.

Module MumbleGrumble.

Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X : Type) : Type :=
  | d (m : mumble)
  | e (x : X).

Fail Check d (b a 5).
Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
Fail Check e bool (b c 0).
Check c : mumble.

End MumbleGrumble.

Fixpoint repeat'' X x count : list X :=
  match count with
  | O    => nil _
  | S n' => cons _ x (repeat'' _ x n')
  end.

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil       => 0
  | cons _ l' => S (length l')
  end.

Inductive list' {X : Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

Definition natnil : @list' nat := nil'.
Definition natnil' := @nil' nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem app_nil_r :
  forall (X : Type) (l : list X), l ++ [] = l.
Proof.
intros.
induction l.
- simpl.
  reflexivity.
- simpl.
  rewrite IHl.
  reflexivity.
Qed.

Theorem app_assoc :
  forall (X : Type) (l1 l2 l3 : list X), l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
intros.
induction l1.
- simpl.
  reflexivity.
- simpl.
  rewrite IHl1.
  reflexivity.
Qed.

Lemma app_length :
  forall (X : Type) (l1 l2 : list X), length (l1 ++ l2) = length l1 + length l2.
Proof.
intros.
induction l1.
- simpl.
  reflexivity.
- simpl.
  rewrite IHl1.
  reflexivity.
Qed.

Theorem rev_app_distr :
  forall X (l1 l2 : list X), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
intros.
induction l1.
- simpl.
  rewrite app_nil_r.
  reflexivity.
- simpl.
  rewrite IHl1.
  rewrite app_assoc.
  reflexivity.
Qed.

Theorem rev_involutive :
  forall X (l : list X), rev (rev l) = l.
Proof.
intros.
induction l.
- simpl.
  reflexivity.
- simpl.
  rewrite rev_app_distr.
  rewrite -> IHl.
  simpl.
  reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _              => []
  | _, []              => []
  | x :: lx', y :: ly' => (x, y) :: combine lx' ly'
  end.

Check @combine.

Compute combine [1;2] [false;false;true].

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | nil          => (nil, nil)
  | (x, y) :: l' =>
    match split l' with
    | (lx', ly') => (x :: lx', y :: ly')
    end
  end.

Compute split [(1, false); (2, true)].

Inductive option (X : Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X}.
Arguments None {X}.

Definition hd_error {X : Type} (l : list X) :=
  match l with
  | nil    => None
  | x :: l => Some x
  end.

Check hd_error.
Check @hd_error.

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | []     => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Fixpoint evenb (n : nat) :=
  match n with
  | O        => true
  | S (S n') => evenb n'
  | _        => false
  end.

Fixpoint gtb (n : nat) (m : nat) :=
  match n, m with
  | O, _       => false
  | _, O       => true
  | S n', S m' => gtb n' m'
  end.

Definition filter_even_gt_7 : list nat -> list nat :=
  filter (fun n => andb (evenb n) (gtb n 7)).

Compute filter_even_gt_7 [1;2;6;9;10;3;12;8].

Fixpoint partition {X : Type} (test : X -> bool) (l : list X) : list X * list X :=
  match l with
  | nil    => ([], [])
  | x :: l' =>
    let
      p' := partition test l'
    in
      (if test x then (x :: (fst p'), snd p') else (fst p', x :: (snd p')))
  end.

Compute partition evenb [1;2;3;4;5].

Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Theorem map_assoc :
  forall (X Y : Type) (f : X->Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
intros.
induction l1.
- simpl.
  reflexivity.
- simpl.
  rewrite IHl1.
  reflexivity.
Qed.

Theorem map_rev :
  forall (X Y : Type) (f : X->Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
intros.
induction l.
- simpl.
  reflexivity.
- simpl.
  rewrite map_assoc.
  rewrite IHl.
  simpl.
  reflexivity.
Qed.

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : list Y :=
  match l with
  | nil     => nil
  | x :: l' => f x ++ flat_map f l'
  end.

Compute flat_map (fun n => [n;n;n]) [1;5;4].

Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil    => b
  | h :: t => f h (fold f t b)
  end.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Compute fold_length [4; 7; 0].

Theorem fold_length_correct :
  forall (X : Type) (l : list X), fold_length l = length l.
Proof.
intros.
induction l.
- simpl.
  unfold fold_length.
  simpl.
  reflexivity.
- simpl.
  unfold fold_length.
  cbn.
  rewrite <- IHl.
  reflexivity.
Qed.

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x l => f x :: l) l [].

Theorem fold_map_correct :
  forall (X Y : Type) (f : X->Y) (l : list X), fold_map f l = map f l.
Proof.
intros.
induction l.
- simpl.
  unfold fold_map.
  simpl.
  reflexivity.
- simpl.
  unfold fold_map.
  simpl.
  rewrite <- IHl.
  reflexivity.
Qed.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (x : X * Y) : Z := f (fst x) (snd x).

Theorem uncurry_curry :
  forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  (prod_curry (prod_uncurry f)) x y = f x y.
Proof.
intros.
unfold prod_uncurry.
unfold prod_curry.
simpl.
reflexivity.
Qed.

Lemma fst_snd_id :
  forall (X Y : Type) (p : X * Y), p = (fst p, snd p).
Proof.
intros.
destruct p.
simpl.
reflexivity.
Qed.

Theorem curry_uncurry :
  forall (X Y Z : Type) (f : X * Y -> Z) p,
  (prod_uncurry (prod_curry f)) p = f p.
Proof.
intros.
unfold prod_curry.
unfold prod_uncurry.
rewrite <- fst_snd_id.
reflexivity.
Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O       => true
  | S n', S m' => eqb n' m'
  | _, _   => false
  end.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | []      => None
     | a :: l' => if eqb n O then Some a else nth_error l' (pred n)
     end.

Lemma length_0_means_empty :
  forall (X : Type) (l : list X), length l = 0 -> l = nil.
Proof.
intros X l.
destruct l.
- simpl.
  reflexivity.
- simpl.
  intros.
  discriminate.  (* S ... = O is false *)
Qed.

Search ">".

Lemma length_non_0_means_full :
  forall (X : Type) (l : list X), not (length l = 0) -> not (l = nil).
Proof.
intros X l.
destruct l.
- simpl.
  intros.
  contradiction.
- intros.
  discriminate.
Qed.

Theorem nth_error_none :
  forall (X : Type) (l : list X) (n : nat), length l = n -> nth_error l n = None.
Proof.
intros X l n.
generalize l.
induction n.
- intros.
  simpl.
  apply length_0_means_empty in H.
  rewrite H.
  simpl.
  reflexivity.
- intros.
  destruct l0.
  + simpl.
    reflexivity.
  + simpl.
    simpl in H.
    injection H.
    intros.
    apply IHn.
    assumption.
Qed.

Module Church.

Definition cnat := forall (X : Type), (X -> X) -> X -> X.

Definition zero : cnat := fun f x => x.

Definition succ (X : Type) (n : cnat) := fun f x => f (n X f x).

Definition plus (n m : cnat) : cnat :=
  fun f x => n f (m f x).

Definition mult (X : Type) (n m : cnat) : cnat :=
  fun X f x => n X (fun x => m X f x) x.

Definition exp (X : Type) (n m : cnat) : cnat. (* TODO *)

End Church.