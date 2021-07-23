---- MODULE Bottles1 ----

EXTENDS Naturals
VARIABLES a, b
CONSTANTS A, B

----

TypeInvariant == /\ a <= A
                 /\ b <= B

InterestingProperty == /\ a # 1
                       /\ b # 1

Invariant == TypeInvariant /\ InterestingProperty

----

Init == a = 0 /\ b = 0

FillA == /\ a' = A
         /\ UNCHANGED b

FillB == /\ b' = B
         /\ UNCHANGED a

EmptyA == /\ a' = 0
          /\ UNCHANGED b

EmptyB == /\ b' = 0
          /\ UNCHANGED a

AtoB == /\ b' = IF a + b <= B THEN a + b ELSE B
        /\ a' = IF a + b <= B THEN 0 ELSE a - (B - b)

BtoA == /\ a' = IF a + b <= A THEN a + b ELSE A
        /\ b' = IF a + b <= A THEN 0 ELSE b - (A - a)

Next == FillA \/ FillB \/ EmptyA \/ EmptyB \/ AtoB \/ BtoA

Spec == Init /\ [][Next]_<<a, b>>

====
