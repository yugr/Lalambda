From mathcomp Require Import ssreflect.

Axiom replace_with_your_solution_here : forall {A : Type}, A.

(* Remember function from the first lecture *)

Definition foo := fun (f : bool -> bool) => f true.

(* We can generalize it a bit *)

Definition applyb : bool -> (bool -> bool) -> bool 
  := fun (b : bool) (f : bool -> bool) => f b.

Definition apply' (A B : Type) :=
  fun (x : A) (f : A -> B) => f x.

Compute apply' bool nat true (fun _ => S O).

Definition apply : forall (A B : Type), A -> (A -> B) -> B :=
  fun (A B : Type) (x : A) (f : A -> B) => f x.

Compute apply bool nat true (fun _ => S O).

(* implement polymorphic version of the apply funtion *)
(* Say about `forall` erasing *)

(* implement parameterized inductive of prod3 *)

Inductive prod3 (A B C : Type) : Type :=
  | triple of A & B & C.

(* Without Coq try to infer `prod3`'s and `triple`'s type *)

Check prod3.
Check triple.

Print triple.
Print prod3.

(* Make implicit some `apply`'s and `triple`'s arguments *)
(* Say about alternative way of Implicit's  *)

(* Introduce a haskell like `$` notation *)

Section Haskell.

(* Local Notation .. := .. . *)

End Haskell.

(* Introduce a (a; b; c) notation for triple *)

(* Notation .. := .. *)


(* function composition *)

Definition comp A B C (f : B -> A) (g : C -> B)  : C -> A :=
  fun c => f (g c).

Notation "f \o g" :=
  (comp f g)
  (at level 50, left associativity).

(* Introduce a notation that lets us use composition like so: f \o g.
   You might need to tweak the implicit status of some comp's arguments *)


(* implement functions with the given signatures *)

Definition fst {A B : Type} : A * B -> A :=
  fun p =>
    match p with
    | (a, _) => a
    end.

Definition snd {A B : Type} : A * B -> B :=
  fun p =>
    match p with
    | pair _ b => b
    end.

Definition prodA (A B C : Type) : (A * B) * C -> A * (B * C) :=
  fun p => pair (fst (fst p)) (pair (snd (fst p)) (snd p)).

Definition prodA' (A B C : Type) : (A * B) * C -> A * (B * C) :=
  fun abc => match abc with
  | ((a, b), c) => (a, (b, c))
  end.

Definition sumA (A B C : Type) :
  (A + B) + C -> A + (B + C) :=
  fun abc => match abc with
  | inl (inl a) => inl a
  | inl (inr b) => inr (inl b)
  | inr c  => inr (inr c)
  end.

Definition prod_sumD (A B C : Type) :
  A * (B + C) -> (A * B) + (A * C) :=
  fun abc => match abc with
  | (a, inl b) => inl (a, b)
  | (a, inr c) => inr (a, c)
  end.

Definition sum_prodD (A B C : Type) :
  A + (B * C) -> (A + B) * (A + C) :=
  fun abc => match abc with
  | inl a      => (inl a, inl a)
  | inr (b, c) => (inr b, inr c)
  end.

(* Introduce `unit` type (a type with exactly one canonical form) *)

(* () : () *)
Inductive unit : Type :=
  | tt.

Definition unit_initial (A : Type) :
  A -> unit
:= fun _ => tt.

(* Introduce empty type, call `void` *)

Inductive void : Type := .

Definition void_terminal (A : Type) :
  void -> A
:= fun v => match v with end.

(* Think of some more type signatures involving void, unit, sum, prod *)
