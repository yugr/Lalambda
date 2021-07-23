From mathcomp Require Import ssreflect.

(*| We continue working with our own definitions of Booleans and natural numbers |*)

Module My.

Inductive bool : Type :=
| true
| false.

Definition negb :=
  fun (b : bool) =>
    match b with
    | true => false
    | false => true
    end.

(** * Exercise 1 : boolean functions *)

(*| 1a. Define `orb` function implementing boolean disjunction and test it
_thoroughly_ using the command `Compute`. |*)

Definition andb (b c : bool) : bool :=
  match b with
  | true => c
  | _ => false
  end.

Definition orb (b c : bool) : bool :=
  match b with
  | true => true
  | _ => c
  end.

Compute orb true false.
Compute orb false false.

Definition orb' (b c : bool) : bool :=
  if b is true then true else c.

(*| 1b. Define `addb` function implementing _exclusive_ boolean disjunction.
Try to come up with more than one definition (try to make it interesting
and don't just swap the variables) and explore its reduction behavior
in the presence of symbolic variables. |*)

Definition addb (b c : bool) : bool :=
  andb (orb b c) (negb (andb b c)).

Compute addb false false.
Compute addb false true.
Compute addb true true.

Definition addb' (b c : bool) : bool :=
  let
    overflow := andb b c
  in
    andb (orb b c) (negb overflow).

Compute addb' false false.
Compute addb' false true.
Compute addb' true true.

(*| 1c. Define `eqb` function implementing equality on booleans, i.e. `eqb b c`
must return `true` if and only iff `b` is equal to `c`. Add unit tests. |*)

Definition eqb (b c : bool) : bool :=
  orb (andb b c) (andb (negb b) (negb c)).

Compute eqb true true.
Compute eqb false false.
Compute eqb true false.

Definition eqb' (b c : bool) : bool :=
  if b is false then negb c else c.

Compute eqb' true true.
Compute eqb false false.
Compute eqb true false.

Definition eqb'' (b c : bool) : bool :=
  match b, c with
  | true, true | false, false => true
  | _, _                      => false
  end.

Compute eqb'' true true.
Compute eqb'' false false.
Compute eqb'' true false.

(** * Exercise 2 : arithmetic *)

Inductive nat : Type :=
| O
| S of nat.


Definition one : nat := S O.
Definition two : nat := S one.
Definition three : nat := S two.
Definition four : nat := S three.
Definition five : nat := S four.
Definition six : nat := S five.

(*| 2a. Define `dec2` function of type `nat -> nat` which takes a natural
number and decrements it by 2, e.g. for the number `5` it must return `3`. Write
some unit tests for `dec2`. What should it return for `1` and `0`? |*)

Definition dec2 (n : nat) : nat :=
  if n is S (S n') then n' else O.

Compute dec2 O.
Compute dec2 one.
Compute dec2 two.
Compute dec2 three.

(*| 2b. Define `subn` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of subtracting `n` from `m`.
E.g. `subn 5 3` returns `2`. Write some unit tests. |*)

Fixpoint subn (m n : nat) : nat :=
  match m, n with
  | S m', S n' => subn m' n'
  | O, _       => O
  | _, O       => m
  end.

Compute subn one O.
Compute subn one one.
Compute subn two one.

Fixpoint addn (m n : nat) : nat :=
  match m with
  | S m' => S (addn m' n)
  | O    => n
  end.

(*| 2c. Define an `muln` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of their multiplication.
Write some unit tests. |*)

Fixpoint muln (m n : nat) : nat :=
  match m with
  | O    => O
  | S m' => addn n (muln m' n)
  end.

Compute muln O two.
Compute muln one two.
Compute muln two two.

(** 2d. Implement equality comparison function `eqn` on natural numbers of
type `nat -> nat -> bool`. It returns true if and only if the input numbers are
equal. *)

Fixpoint eqn (m n : nat) : bool :=
  match m, n with
  | O, S _     => false
  | S _, O     => false
  | O, O       => true
  | S m', S n' => eqn m' n'
  end.

Compute eqn O one.
Compute eqn one one.
Compute eqn O O.

(** 2e. Implement less-or-equal comparison function `leq` on natural numbers of
type `nat -> nat -> bool`. `leq m n` returns `true` if and only if `m` is less
than or equal to `n`. Your solution must not use recursion but you may reuse any
of the functions you defined in this module so far. *)

Fixpoint leq' (m n : nat) : bool :=
  match m, n with
  | O, _       => true
  | S _, O     => false
  | S m', S n' => leq' m' n'
  end.

Definition leq (m n : nat) : bool :=
  eqn (subn m n) O.

Compute leq O one.
Compute leq O O.
Compute leq one O.

(*| ---------------------------------------------------------------------------- |*)


(*| EXTRA problems: feel free to skip these. If you need to get credit for this
class: extra exercises do not influence your grade negatively if you skip them.
|*)

(*| Ea: implement division (`divn`) on natural numbers and write some unit tests
for it. |*)

Definition lt (m n : nat ) : bool :=
  andb (leq m n) (negb (eqn m n)).

Fixpoint div_helper (m n dummy : nat) {struct dummy} :=
  if dummy is S dummy' then
    if lt m n is true then
      O
    else
      S (div_helper (subn m n) n dummy')
  else
    O.

Definition div (m n : nat) := div_helper m n m.

Compute eqn two (div two O).
Compute eqn three (div six two).
Compute eqn three (div six two).
Compute eqn one (div three two).

End My.
