---- MODULE PrintValues ----
EXTENDS Naturals, TLC, Sequences, Reals
PrintVal(id, exp) == Print(<<id, exp>>, TRUE)
----
ASSUME
  /\ PrintVal("1.1", {i \in 1..10 : \E j \in 1..10 : i = j^2})
  /\ PrintVal("1.2", {i \in 1..10 : \E j \in 1..10 : j = i^2})
  /\ PrintVal("1.3", {i^2 : i \in 1..10})
  /\ PrintVal("1.4", {i^2 + j : i, j \in 1..3})
  /\ PrintVal("1.5", {<<i^2, j^2>> : i \in 1..2, j \in 2..3})
  /\ PrintVal("1.6", UNION {{i^2} : i \in 1..10})
  /\ PrintVal("1.7", UNION {{{i^2}} : i \in 1..10})
  (* /\ PrintVal("1.6", UNION SUBSET S (for any S)) *)
  /\ PrintVal("1.8", SUBSET DOMAIN [a |-> 1, b |-> 2])
  /\ PrintVal("1.9", SUBSET [a : {1}, b : {2}])
  /\ PrintVal("1.10", CHOOSE n \in 1..100 : n^2 = 49)

Foldr(op(_, _), s, val) ==
  LET FoldrImpl[i \in Nat] ==
    IF i = 0 THEN val ELSE op(FoldrImpl[i - 1], s[i])
  IN FoldrImpl[Len(s)]

ASSUME PrintVal("2.1", LET Plus(a, b) == a + b IN Foldr(Plus, <<1, 2, 3>>, 0))

Foldl(op(_, _), s, val) ==
  LET FoldlImpl[i, acc \in Nat] ==
   IF i > Len(s) THEN acc ELSE FoldlImpl[i + 1, op(acc, s[i])]
  IN FoldlImpl[1, val]

ASSUME PrintVal("2.1", LET Plus(a, b) == a + b IN Foldl(Plus, <<1, 2, 3>>, 0))

(* 3.a can't be defined because we can't defined domain *)

f3b[S \in SUBSET Real] == CHOOSE x \in S : \A y \in S : x >= y
f3b_other == [S \in SUBSET Real |-> CHOOSE x \in S : \A y \in S : x >= y]

f3a[n \in Nat] == IF n = 0 THEN 1 ELSE n * f3a[n + 1]

====
