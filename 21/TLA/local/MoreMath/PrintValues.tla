---- MODULE PrintValues ----
EXTENDS Naturals, TLC, Sequences
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

RECURSIVE Apply(_, _, _)
\* Why this does not work?! Apply(op(_, _), s, val) == IF s == << >> THEN val ELSE Apply(op, Tail(s), op(val, Head(s)))
Apply(op(_, _), s, val) == IF s = << >> THEN val ELSE Apply(op, Tail(s), op(Head(s), val))

====
