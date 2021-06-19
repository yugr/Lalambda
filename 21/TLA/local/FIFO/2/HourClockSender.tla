---- MODULE HourClockSender ----
EXTENDS HourClockReset, Channel
SenderTypeInvariant ==
  /\ HCinv
  /\ TypeInvariant
  /\ chan \in [val : Month, rdy : {0, 1}, ack : {0, 1}]
----
SenderInit == HCini /\ Init
SenderNext == HCnxt /\ (Send(hr) \/ Rcv)
(* SenderNext ==
  \/ chan.rdy = chan.ack /\ HCnxt /\ UNCHANGED chan
  \/ (Send(hr) \/ Rcv) /\ UNCHANGED <<hr, reset, hr_set>> *)
SenderSpec == SenderInit /\ [][SenderNext]_<<chan, hr, reset, hr_set>>
----
THEOREM SenderSpec => []SenderTypeInvariant
====
