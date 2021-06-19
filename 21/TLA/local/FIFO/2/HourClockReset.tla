---------------------- MODULE HourClockReset ----------------------
EXTENDS Naturals
VARIABLE hr, reset, hr_set
Month == 1 .. 12
HCinv ==
  /\ hr \in Month
  /\ reset \in {0, 1}
  /\ hr_set \in Month  \* TODO: hide hr_set ?
----
HCini == HCinv
Reset == reset = 1 /\ hr' = hr_set
Increment == reset = 0 /\ hr' = IF hr # 12 THEN hr + 1 ELSE 1
EnvNext ==
  /\ (\E r \in {0, 1} : reset' = reset)
  /\ (\E hs \in Month : hr_set' = hs)
SysNext == Reset \/ Increment
HCnxt == EnvNext /\ SysNext
HC    == HCini /\ [][HCnxt]_<<hr, reset, hr_set>>
----
THEOREM HC => []HCinv
==============================================================
