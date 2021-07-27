---- MODULE Bottles1 ----

EXTENDS Naturals
VARIABLES a, b
CONSTANTS A, B, goal

----

TypeInvariant == /\ a <= A
                 /\ b <= B

\* We need 'goal' in one of the bottles
NotGoal == /\ a # goal
           /\ b # goal

Invariant == TypeInvariant /\ NotGoal

----

Max(x, y) == IF x > y THEN x ELSE y
Min(x, y) == IF x < y THEN x ELSE y

----

Init == a = 0 /\ b = 0

FullA == /\ a' = A
         /\ UNCHANGED b

FullB == /\ b' = B
         /\ UNCHANGED a

EmptyA == /\ a' = 0
          /\ UNCHANGED b

EmptyB == /\ b' = 0
          /\ UNCHANGED a

AtoB == /\ b' = Min(a + b, B)
        /\ a' = Max(0, a - (B - b))

BtoA == /\ a' = Min(a + b, A)
        /\ b' = Max(0, b - (A - a))

Next == \/ FullA
        \/ FullB
        \/ EmptyA
        \/ EmptyB
        \/ AtoB
        \/ BtoA

Spec == Init /\ [][Next]_<<a, b>>

====
