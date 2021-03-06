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
  | nil    => l2
  | x :: l1' =>
    match l2 with
    | y :: l2' => x :: y :: alternate l1' l2'
    | nil      => x :: alternate l1' l2
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

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Theorem app_assoc :
  forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
intros l1 l2 l3.
induction l1 as [| n l1' IHl1'].
- (* l1 = nil *)
  reflexivity.
- (* l1 = cons n l1' *)
  simpl.
  rewrite -> IHl1'.
  reflexivity.
Qed.

Theorem app_nil_r :
  forall (l : natlist), l ++ [] = l.
Proof.
intros.
induction l as [|n l' IHl'].
- simpl.
  reflexivity.
- simpl.
  rewrite -> IHl'.
  reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Theorem rev_app_distr :
  forall (l1 l2 : natlist),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
intros.
induction l1 as [|n l1' IHl'].
- simpl.
  rewrite app_nil_r.
  reflexivity.
- simpl.
  rewrite IHl'.
  rewrite app_assoc.
  reflexivity.
Qed.

Theorem rev_head :
  forall (l : natlist) (n : nat),
  rev (n :: l) = rev l ++ [n].
Proof.
intros l.
induction l as [|x l' IHl'].
- simpl.
  reflexivity.
- intros.
  simpl.
  reflexivity.
Qed.

Theorem rev_involutive :
  forall (l : natlist), rev (rev l) = l.
Proof.
intros.
induction l as [|n l' IHl'].
- simpl.
  reflexivity.
- simpl.
  rewrite rev_app_distr.
  rewrite IHl'.
  simpl.
  reflexivity.
Qed.

Theorem app_assoc4 :
  forall (l1 l2 l3 l4 : natlist),
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
intros.
rewrite app_assoc.
rewrite app_assoc.
reflexivity.
Qed.

Lemma nonzeros_app :
  forall (l1 l2 : natlist),
  nonzeros (l1 ++ l2) = nonzeros l1 ++ nonzeros l2.
Proof.
intros.
induction l1 as [|n l1' IHl'].
- simpl.
  reflexivity.
- destruct n.
  + simpl.
    rewrite IHl'.
    reflexivity.
  + simpl.

    rewrite IHl'.
    reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil             => true
  | x1 :: l1', x2 :: l2' => if eqb x1 x2 then eqblist l1' l2' else false
  | _, _                 => false
  end.

Theorem eqb_refl :
  forall (n : nat), eqb n n = true.
Proof.
induction n.
- simpl.
  reflexivity.
- simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem eqblist_refl :
  forall (l : natlist),
  eqblist l l = true.
Proof.
intros.
induction l as [|n l' IHl'].
- simpl.
  reflexivity.
- destruct n.
  + simpl.
    rewrite IHl'.
    reflexivity.
  + simpl.
    rewrite eqb_refl.
    rewrite IHl'.
    reflexivity.
Qed.

Fixpoint leb (n m : nat) :=
  match n, m with
  | O, O => true
  | S _, O => false
  | O, S _ => true
  | S n', S m' => leb n' m'
  end.

Notation "x <=? y" := (leb x y) (at level 60).

Theorem count_member_nonzero :
  forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
intros.
simpl.
destruct (count 1 s); reflexivity.
Qed.

Theorem leb_n_Sn :
  forall n, n <=? S n = true.
Proof.
intros.
induction n as [|n' IHn'].
- simpl.
  reflexivity.
- simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Theorem remove_does_not_increase_count :
  forall (s : bag), count 0 (remove1 0 s) <=? (count 0 s) = true.
Proof.
intros.
induction s as [|n s' IHs'].
- simpl.
  reflexivity.
- destruct n.
  + simpl.
    rewrite leb_n_Sn.
    reflexivity.
  + simpl.
    rewrite IHs'.
    reflexivity.
Qed.

Theorem bag_count_sum :
  forall (a b : bag) (n : nat), count n (sum a b) = count n a + count n b.
Proof.
intros.
induction a as [|x a' IHa'].
Admitted. (* TODO *)

Lemma cons_is_app :
  forall (l : natlist) (n : nat), n :: l = [n] ++ l.
Proof.
intros.
induction l; simpl; reflexivity.
Qed.

Lemma cons_app_commute :
  forall (l1 l2 : natlist) (n : nat), (n :: l1) ++ l2 = n :: (l1 ++ l2).
Proof.
intros.
rewrite -> cons_is_app.
assert (n :: l1 ++ l2 = [n] ++ (l1 ++ l2)).
- rewrite cons_is_app. reflexivity.
- rewrite -> H.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma app1_not_empty :
  forall (l : natlist) (n : nat), not (l ++ [n] = []).
Proof.
intros.
induction l.
- simpl.
  discriminate.
- rewrite cons_app_commute.
  discriminate.
Qed.

Lemma rev_empty :
  forall (a : natlist), rev a = [] -> a = [].
Proof.
intro.
destruct a.
- simpl.
  intros.
  reflexivity.
- simpl.
  intros.
  exfalso.
  apply app1_not_empty in H.
  assumption.
Qed.

Theorem rev_injective :
  forall (a b : natlist), rev a = rev b -> a = b.
Proof.
intros a.
induction a.
- simpl.
  symmetry.
  symmetry in H.
  apply rev_empty.
  assumption.
- destruct b.
  + assert (rev [] = []).
    * simpl. reflexivity.
    * rewrite H.
      apply rev_empty.
  + (* rev (n :: a) = rev (n0 :: b) -> n :: a = n0 :: b *)
Admitted.

Theorem rev_injective_simple :
  forall (a b : natlist), rev a = rev b -> a = b.
Proof.
intros.
assert (rev (rev a) = rev (rev b)).
- rewrite H.
  reflexivity.
- rewrite rev_involutive in H0.
  rewrite rev_involutive in H0.
  assumption.
Qed.

(* New stuff: symmetry, exfalso, apply ... in ... VS rewrite *)

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil     => None
  | a :: l' => match n with
               | O    => Some a
               | S n' => nth_error l' n'
               end
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None    => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil    => None
  | x :: _ => Some x
  end.

Definition hd (d : nat) (l : natlist) :=
  match l with
  | nil    => d
  | x :: _ => x
  end.

Theorem optional_elimit_hd :
  forall (l : natlist) (d : nat), hd d l = option_elim d (hd_error l).
Proof.
intros.
induction l; simpl; reflexivity.
Qed.

(* Remaining tasks too simple *)