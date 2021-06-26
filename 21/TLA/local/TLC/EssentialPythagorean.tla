---- MODULE EssentialPythagorean ----
EXTENDS Naturals, TLC
VARIABLES i, j, k
----
PInit == i = 1 /\ j = 1 /\ k = 1
PNext ==
  \/ i' = i + 1 /\ UNCHANGED <<j, k>>
  \/ j' = j + 1 /\ UNCHANGED <<i, k>>
  \/ k' = k + 1 /\ UNCHANGED <<i, j>>
IsPythagorean == i^2 + j^2 = k^2
Largest ==
  CASE i > j /\ i > k -> i
    [] j > i /\ j > k -> j
    [] OTHER          -> k
IsEssentialPythagorean ==
  /\ IsPythagorean
  /\ i \leq j /\ j \leq k
  /\ ~ \E x \in (2..Largest) : i % x = 0 /\ j % x = 0 /\ k % x = 0
PNextAndPrint ==
  PNext
  /\ IF IsEssentialPythagorean THEN Print(<<i, j, k>>, TRUE) ELSE TRUE
PSpec == PInit /\ [][PNextAndPrint]_<<i, j, k>>
====
