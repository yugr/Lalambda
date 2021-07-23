---- MODULE HourClockSender ----
EXTENDS HourClock, Channel
SenderTypeInvariant ==
  /\ HCinv
  /\ TypeInvariant
  /\ chan \in [val : Month, rdy : {0, 1}, ack : {0, 1}]
----
SenderInit == HCini /\ Init
\* SenderNext == HCnxt /\ (Send(hr) \/ Rcv)
SenderNext ==
  \/ chan.rdy = chan.ack /\ HCnxt /\ UNCHANGED chan
  \/ (Send(hr) \/ Rcv) /\ UNCHANGED hr
SenderSpec == SenderInit /\ [][SenderNext]_<<chan, hr>>
----
THEOREM SenderSpec => []SenderTypeInvariant
====
