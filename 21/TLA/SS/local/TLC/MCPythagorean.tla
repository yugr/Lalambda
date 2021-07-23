---- MODULE MCPythagorean ----
EXTENDS Pythagorean
CONSTANT N
----
LimitConstraint == i <= N /\ j <= N /\ k <= N
====
