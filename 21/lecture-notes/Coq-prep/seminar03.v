Axiom replace_with_your_solution_here : forall {A : Type}, A.

Section PropositionalLogic.

Variables A B C : Prop.

Definition anb1 :
  A /\ B -> A
:= fun aAb =>
  match aAb with
  | conj a b => a
  end.

Definition impl_trans :
  (A -> B) -> (B -> C) -> A -> C
:= fun aTb bTc a => bTc (aTb a).

Definition HilbertS :
  (A -> B -> C) -> (A -> B) -> A -> C
:= fun aTbTc aTb a => aTbTc a (aTb a).

Definition double_negation_introduction (A : Prop) :
   A -> ~ ~ A
:= fun pa : A => fun pna : ~ A => pna pa.

Definition DNE_triple_neg (A : Prop) :
  ~ ~ ~ A -> ~ A
:= fun nnna => fun a => nnna (double_negation_introduction A a).

Definition DNE_triple_neg' (A : Prop) :
  ~ ~ ~ A -> ~ A
:= fun nnna a => nnna ((fun na : ~ A => na a) : ~ ~ A).

Definition or_comm :
  A \/ B -> B \/ A
:= fun aVb => match aVb with
  | or_introl a => or_intror a
  | or_intror b => or_introl b
  end.

End PropositionalLogic.



Section Quantifiers.

Variable T : Type.
Variable A : Prop.
Variable P Q : T -> Prop.

Definition forall_conj_comm :
  (forall x : T, P x /\ Q x) <-> (forall x : T, Q x /\ P x)
:= conj
  (fun pAq x => match pAq x with | conj px qx => conj qx px end)
  (fun qAp x => match qAp x with | conj qx px => conj px qx end).

Definition forall_disj_comm :
  (forall x, P x \/ Q x) <-> (forall x, Q x \/ P x)
:= conj
  (fun pVq x => match pVq x with
     | or_introl px => or_intror px
     | or_intror qx => or_introl qx
   end)
  (fun qVp x => match qVp x with
     | or_introl qx => or_intror qx
     | or_intror px => or_introl px
   end).

Definition not_exists_forall_not :
  ~(exists x, P x) -> forall x, ~P x
:= fun nEp x px => nEp (ex_intro P x px).

(* Can't use `P` in ex_intro pattern due to
  "The parameters do not bind in patterns; they must be replaced by '_'." *)
Definition exists_forall_not_ :
  (exists x, A -> P x) -> (forall x, ~P x) -> ~A
:= fun '(ex_intro _ x aTpx) Unp a =>
  Unp x (aTpx a).

(** Extra exercise (feel free to skip): the dual Frobenius rule *)
Definition LEM :=
  forall P : Prop, P \/ ~ P.

Definition Frobenius2 :=
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x, Q \/ P x) <-> (Q \/ forall x, P x).

(* TODO
Definition lem_iff_Frobenius2 :
  LEM <-> Frobenius2 *)

Definition lem_iff_Frobenius2_forward :
(*  LEM -> (forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x, Q \/ P x) <-> (Q \/ forall x, P x)) *)
  LEM -> Frobenius2
:= fun Lem A P Q =>
  conj
    (fun U_qVp =>
      match Lem Q with
      | or_introl q  => or_introl q
      | or_intror nq => or_intror (
        fun x => match U_qVp x with
          | or_introl q => (match nq q with end)
          | or_intror px => px
        end)
      end
    )
    (fun qVUp => (fun x => match qVUp with
      | or_introl q => or_introl q
      | or_intror p => or_intror (p x)
      end)).

Definition lem_iff_Frobenius2_backward :
  Frobenius2 -> LEM
(*  (forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x, Q \/ P x) <-> (Q \/ forall x, P x)
  ) -> (forall P : Prop, P \/ ~ P) *)
:= fun Frob P => match Frob P (fun _ => False) P with
  | conj a _ => a (fun p => or_introl p)
  end.

End Quantifiers.

Section Equality.

(** exercise: *)
Definition f_congr {A B} (f : A -> B) (x y : A) :
  x = y  ->  f x = f y
:=

Definition f_congr' A B (f g : A -> B) (x y : A) :
  f = g  ->  x = y  ->  f x = g y
:=

(** extra exercise *)
Definition congId A {x y : A} (p : x = y) :
  f_congr (fun x => x) p = p :=

(* exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:=

End Equality.



Section ExtensionalEqualityAndComposition.

Variables A B C D : Type.

(** Exercise 2a *)
(** [\o] is a notation for function composition in MathComp, prove that it's associative *)

Definition compA (f : A -> B) (g : B -> C) (h : C -> D) :
  (h \o g) \o f = h \o (g \o f)
:=


(** [=1] stands for extensional equality on unary functions,
    i.e. [f =1 g] means [forall x, f x = g x].
    This means it's an equivalence relation, i.e. it's reflexive, symmetric and transitive.
    Let us prove a number of facts about [=1]. *)


(** Exercise: Reflexivity *)
Definition eqext_refl :
  forall (f : A -> B), f =1 f
:=

(** Exercise: Symmetry *)
Definition eqext_sym :
  forall (f g : A -> B), f =1 g -> g =1 f
:=

(** Exercise: Transitivity *)
Definition eqext_trans :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
:=

(** Exercise: left congruence *)
Definition eq_compl :
  forall (f g : A -> B) (h : B -> C),
    f =1 g -> h \o f =1 h \o g
:=

(** Exercise: right congruence *)
Definition eq_compr :
  forall (f g : B -> C) (h : A -> B),
    f =1 g -> f \o h =1 g \o h
:=

End ExtensionalEqualityAndComposition.


From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

(* After importing `eqtype` you need to either use a qualified name for
`eq_refl`: `Logic.eq_refl`, or use the `erefl` notation.
This is because `eqtype` reuses the `eq_refl` identifier for a
different lemma.
 *)

Definition iff_is_if_and_only_if :
  forall a b : bool, (a ==> b) && (b ==> a) = (a == b)
:=

Definition negbNE :
  forall b : bool, ~~ ~~ b = true -> b = true