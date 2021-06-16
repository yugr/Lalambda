Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Notation "( x , y )" := (pair x y).

Definition fst (p : natprod) : nat :=
  match p with
  | (x, _) => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | (_, y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Compute fst (pair 3 5).

Theorem snd_fst_is_swap :
  forall (p : natprod), (snd p, fst p) = swap_pair p.
Proof.
intros.
destruct p.
simpl.
reflexivity.
Qed.

Theorem fst_swap_is_snd :
  forall (p : natprod), fst (swap_pair p) = snd p.
Proof.
intros.
destruct p.
simpl.
reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | nil    => nil
  | O :: l => nonzeros l
  | x :: l => x :: nonzeros l
  end.

Compute nonzeros [0;1;0;2;0;3;0;4].

Fixpoint oddmembers' (l : natlist) : natlist :=
  match l with
  | nil          => nil
  | x :: nil     => l
  | x :: y :: l' => x :: oddmembers' l'
  end.

Compute oddmembers' [0;1;0;2;0;3;0;4].

Fixpoint odd (n : nat) : bool :=
  match n with
  | O       => false
  | S O     => true
  | S (S x) => odd x
  end.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | nil    => nil
  | x :: l => if odd x then x :: oddmembers l else oddmembers l
  end.

Compute oddmembers [0;1;0;2;0;3;0;4].

Fixpoint add (n m : nat) : nat :=
  match n with
  | O    => m
  | S n' => add n' (S m)
  end.

Fixpoint countmembers (l : natlist) : nat :=
  match l with
  | nil    => O
  | x :: l => add x (countmembers l)
  end.

Compute countmembers [0;1;0;2;0;3;0;4].

Definition tl (l : natlist) : natlist :=
  match l with
  | nil     => nil
  | _ :: l' => l'
  end.

(* TODO: how to do this? *)
Fail Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => nil
  | x :: l1' =>
    match l2 with
    | _ :: l2' => x :: alternate l2' l1'
    | nil      => nil
    end
  end.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => nil
  | x :: l1' =>
    match l2 with
    | y :: l2' => x :: y :: alternate l1' l2'
    | nil      => nil
    end
  end.

Compute alternate [1;2;3] [4;5;6].

Definition bag := natlist.

(* TODO: how to do this? *)
Fail Fixpoint count (v : nat) (l : natlist) : nat :=
  match l with
  | nil     => O
  | v :: l' => S (count v l')
  | _ :: l' => count v l'
  end.

Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | S n', O    => false
  | O, S m'    => false
  | O, O       => true
  | S n', S m' => eqb n' m'
  end.

Fixpoint count (v : nat) (l : natlist) : nat :=
  match l with
  | nil     => O
  | x :: l' => if eqb x v then S (count v l') else count v l'
  end.

Compute count 1 [1;2;1].

Definition sum : bag -> bag -> bag := alternate.

Compute sum [1; 2; 3] [1; 4; 1].

Definition add' (v : nat) (s : bag) := cons v s.

Definition member (v : nat) (s : bag) : bool :=
  if count v s then false else true.

Compute member 1 [1;2;3].
Compute member 1 [0;2;3].

Fixpoint remove1 (v : nat) (s : bag) : bag :=
  match s with
  | x :: s' => if eqb x v then s' else x :: remove1 v s'
  | nil     => nil
  end.

Compute remove1 1 [1;1;2].

Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
  | x :: s' => if eqb x v then remove_all v s' else x :: remove_all v s'
  | nil     => nil
  end.

Compute remove_all 1 [1;1;2].

Lemma eqb_reflexivity :
  forall (n : nat), eqb n n = true.
Proof.
intros.
induction n as [|n' IHn'].
- simpl.
  reflexivity.
- simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Theorem bag_theorem :
  forall (v : nat) (s : bag), count v (add' v s) = S (count v s).
Proof.
intros.
unfold add'.
simpl.
rewrite eqb_reflexivity.
reflexivity.
Qed.