---------------------- MODULE HourClock ----------------------
EXTENDS Naturals
VARIABLE hr
Month == 1 .. 12
HCinv == hr \in Month
----
HCini == hr \in Month
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC    == HCini /\ [][HCnxt]_hr
----
THEOREM HC => []HCinv
==============================================================
