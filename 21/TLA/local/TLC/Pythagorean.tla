---- MODULE Pythagorean ----
EXTENDS Naturals, TLC
VARIABLES i, j, k
----
PInit == i = 1 /\ j = 1 /\ k = 1
PNext ==
  \/ i' = i + 1 /\ UNCHANGED <<j, k>>
  \/ j' = j + 1 /\ UNCHANGED <<i, k>>
  \/ k' = k + 1 /\ UNCHANGED <<i, j>>
IsPythagorean == i^2 + j^2 = k^2
PNextAndPrint ==
  PNext
  /\ IF IsPythagorean THEN Print(<<i, j, k>>, TRUE) ELSE TRUE
PSpec == PInit /\ [][PNextAndPrint]_<<i, j, k>>
====
