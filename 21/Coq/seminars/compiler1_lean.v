(*|
##############################################
 A compiler from expressions to stack machine
##############################################
|*)

(*|

.. contents:: Table of Contents

|*)

From QuickChick Require Import QuickChick.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify. (* lia *)
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Global Set Bullet Behavior "None".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*|
*******************************
 Simple Arithmetic Expressions
******************************* |*)

Module ArithExpr.

(*|
Expressions
=========== |*)

(*|
Abstract Syntax Tree
-------------------- |*)

(*| Abstract Syntax Tree (AST) for arithmetic expressions: we support numerals
(`Const`) and three arithmetic operations: addition (represented with the `Plus`
constructor), truncating subtraction (`Minus`), multiplication (`Mult`). |*)

Inductive aexp : Type :=
| Const of nat
| Plus of aexp & aexp
| Minus of aexp & aexp
| Mult of aexp & aexp.

(*| QuickChick (see below) comes with a derivation mechanism for random
generators and conversion to strings for a wide class of inductive types. |*)
Derive (Arbitrary, Show) for aexp.

Implicit Types (e : aexp).

(*|
Evaluator
========= |*)

Section Evaluator.

(*| Computable big-step semantics for arithmetic expressions: |*)
Fixpoint aeval (e : aexp) : nat :=
  match e with
  | Const n     => n
  | Plus e1 e2  => aeval e1 + aeval e2
  | Minus e1 e2 => aeval e1 - aeval e2
  | Mult e1 e2  => aeval e1 * aeval e2
  end.

End Evaluator.

(*| Unit and notation tests: |*)
Check erefl : aeval (Minus (Const 0) (Const 4)) = 0.
Check erefl : aeval (Minus (Minus (Const 40) (Const 3)) (Const 1)) = 36.
Check erefl : aeval (Minus (Const 40) (Minus (Const 3) (Const 1))) = 38.
Check erefl : aeval (Plus (Const 2) (Mult (Const 2) (Const 2))) = 6.
Check erefl : aeval (Mult (Plus (Const 2) (Const 2)) (Const 2)) = 8.
Check erefl : aeval (Minus (Plus (Const 40) (Const 3)) (Const 1)) = 42.


(*|
Simple Stack Machine
==================== |*)

(*|
Abstract Syntax for Simple Stack Machine
---------------------------------------- |*)

(*| The stack machine instructions: |*)
Inductive instr := Push (n : nat) | Add | Sub | Mul.


(*| QuickChick (see below) comes with a derivation mechanism for random
generators and conversion to strings for a wide class of inductive types. |*)
Derive (Arbitrary, Show) for instr.

(*| A program for our stack machine is simply a sequence of instructions: |*)
Definition prog := seq instr.

(*| The stack of our stack machine is represented as a list of natural numbers |*)
Definition stack := seq nat.

Implicit Types (p : prog) (s : stack).

(*|
Stack Programs Semantics
------------------------ |*)

Fixpoint run p s : stack :=
  match p, s with
  | (Push n) :: p, s          => run p (n :: s)
  | Add :: p, (a1 :: a2 :: s) => run p ((a2 + a1) :: s)
  | Sub :: p, (a1 :: a2 :: s) => run p ((a2 - a1) :: s)
  | Mul :: p, (a1 :: a2 :: s) => run p ((a2 * a1) :: s)
  | _ :: p, s                 => run p s
  | _, _                      => s
  end.

Arguments run : simpl nomatch.

(*| Unit and notation tests: |*)
Check erefl : run [:: Push 21; Push 21; Add] [::] = [:: 42].


(*|
Compiler from Simple Arithmetic Expressions to Stack Machine Language
===================================================================== |*)

Fixpoint compile e : prog :=
  match e with
  | Const n     => [:: Push n]
  | Plus e1 e2  => compile e1 ++ compile e2 ++ [:: Add]
  | Minus e1 e2 => compile e1 ++ compile e2 ++ [:: Sub]
  | Mult e1 e2  => compile e1 ++ compile e2 ++ [:: Mul]
  end.

Check erefl: run (compile (Minus (Plus (Const 40) (Const 3)) (Const 1))) [::] = [:: 42].

(*|
Property-based randomized testing
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ |*)
(*
+++ Passed 10000 tests (0 discards)
*)

(*|
Compiler correctness: specification and first steps to prove it
--------------------------------------------------------------- |*)

(* TODO: maybe show the non-generalized version first *)

QuickChick (fun (a : instr) l s  =>
  run (cons a l) s == run l (run (cons a nil) s)).

Lemma run_cons_comm a l s :
  run (a :: l) s = run l (run (cons a nil) s).
Proof.
case: a.
- move=> n /=.
  exact: erefl.
- (* Proove for Plus *)
  case: s.
  + by [].
  + move=> a1 l1 /=.
    case: l1.
    * by [].
    * move=> a2 l2 /=.
      exact: erefl.
- (* Proove for Minus *)
  case: s.
  + by [].
  + move=> a1 l1 /=.
    case: l1.
    * by [].
    * move=> a2 l2 /=.
      exact: erefl.
- (* Proove for Mult *)
  case: s.
  + by [].
  + move=> a1 l1 /=.
    case: l1.
    * by [].
    * move=> a2 l2 /=.
      exact: erefl.
Qed.

Lemma run_cons_comm' a l s :
  run (a :: l) s = run l (run (cons a nil) s).
Proof.
case: a.
- move=> n /=.
  exact: erefl.
all: case: s => // a1 l1 //; case: l1 => // a2 l2 /=; exact: erefl.
Qed.

QuickChick (fun (p1 p2 : prog) s  =>
  run (p1 ++ p2) s == run p2 (run p1 s)).

Lemma run_cat_comm :
  forall p1 p2 s, run (p1 ++ p2) s = run p2 (run p1 s).
Proof.
elim => /=.
- move=> p2 s.
  exact: erefl.
- move=> a l IHl /= p2 s.
  rewrite run_cons_comm.
  rewrite IHl.
  rewrite -run_cons_comm.
  exact: erefl.
Qed.

Theorem compile_correct_helper e :
  forall s, run (compile e) s = (aeval e) :: s.
Proof.
elim: e.
- by [].
- (* Proove for Plus *)
  move=> e1 IHe1 e2 IHe2 s /=.
  rewrite run_cat_comm.
  rewrite IHe1.
  rewrite run_cat_comm.
  rewrite IHe2.
  rewrite /IHe2.
  move => /=.
  exact: erefl.
- (* Proove for Minus *)
  move=> e1 IHe1 e2 IHe2 s /=.
  rewrite run_cat_comm.
  rewrite IHe1.
  rewrite run_cat_comm.
  rewrite IHe2.
  rewrite /IHe2.
  move => /=.
  exact: erefl.
- (* Proove for Mult *)
  move=> e1 IHe1 e2 IHe2 s /=.
  rewrite run_cat_comm.
  rewrite IHe1.
  rewrite run_cat_comm.
  rewrite IHe2.
  rewrite /IHe2.
  move => /=.
  exact: erefl.
Qed.

Theorem compile_correct_helper' e :
  forall s, run (compile e) s = (aeval e) :: s.
Proof.
elim: e=> // e1 IHe1 e2 IHe2 s /=; rewrite ?run_cat_comm IHe1 IHe2 //=.
Qed.

Theorem compile_correct_helper'' e :
  forall s, run (compile e) s = (aeval e) :: s.
Proof.
elim: e.
- by [].
all: move=> e1 IHe1 e2 IHe2 s /=; rewrite ?run_cat_comm IHe1 IHe2 //=.
Qed.

Theorem compile_correct e :
  run (compile e) nil = [ :: aeval e ].
Proof.
exact: (compile_correct_helper e nil).
Qed.

(*|
Compiler is not very inefficient
-------------------------------- |*)

(*| Let us show the compiler does not produce very inefficient code: we are
going to assume that the measure of inefficiency in our case is the length of
the code the compiler produces. In our case the length of produced code should
not exceed the number of symbols (operations and constants) in the source
arithmetic expression. In fact, our compiler is efficient in a sense, for
instance, it does not add spurious instructions like `<some-code>; ⧐ 0; ⊕; ...`
but our specification so far does not ensure that. |*)

Fixpoint nsymb (e : aexp) : nat :=
  match e with
  | Const n                               => 1
  | Plus e1 e2 | Minus e1 e2 | Mult e1 e2 => S (nsymb e1 + nsymb e2)
  end.

(*| First, let's check the property holds using QuickChick: |*)

Print size.

QuickChick (fun e =>
  size (compile e) <= nsymb e).

Lemma compile_is_not_very_inefficient e :
  size (compile e) <= nsymb e.
Proof.
elim: e => // => e1 IHe1 e2 IHe2 /=.
- rewrite ?size_cat => /=.
  rewrite addnA addn1.
  apply: leq_ltS (leq_add IHe1 IHe2).
- rewrite ?size_cat => /=.
  rewrite addnA addn1.
  apply: leq_ltS (leq_add IHe1 IHe2).
- rewrite ?size_cat => /=.
  rewrite addnA addn1.
  apply: leq_ltS (leq_add IHe1 IHe2).
Qed.

Lemma compile_is_not_very_inefficient' e :
  size (compile e) <= nsymb e.
Proof.
elim: e => // e1 IHe1 e2 IHe2 /=;
  rewrite ?size_cat => /=;
  rewrite addnA addn1;
  apply: leq_ltS (leq_add IHe1 IHe2).
Qed.

End ArithExpr.