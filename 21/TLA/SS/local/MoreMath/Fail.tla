---- MODULE Fail ----
EXTENDS Sequences
----
RECURSIVE Apply1(_, _)
Apply1(f(_), x) == f(x)

(* Fails with "Definition of Apply2 has different arity than its RECURSIVE declaration" *)
\* RECURSIVE Apply2(_, _)
\* Apply2(x, f(_)) == f(x)

RECURSIVE Fold1(_, _, _)
Fold1(op(_, _), s, val) ==  IF s = << >> THEN val ELSE Fold1(op, Tail(s), op(val, Head(s)))

RECURSIVE Fold2(_, _, _)
Fold2(op(_, _), s, val) ==  IF s = << >> THEN val ELSE Fold2(op, Tail(s), op(Head(s), val))

(* Fails with "Definition of Fold3 has different arity than its RECURSIVE declaration" *)
\* RECURSIVE Fold3(_, _, _)
\* Fold3(s, val, op(_, _)) ==  IF s = << >> THEN val ELSE Fold3(Tail(s), op(Head(s), val), op)

====
