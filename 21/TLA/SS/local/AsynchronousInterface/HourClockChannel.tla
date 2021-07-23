-------------------------- MODULE HourClockChannel -----------------------------
EXTENDS Naturals, HourClock
(* EXTENDS HourClock *)

CONSTANT Data
VARIABLE chan 

TypeInvariant  ==  chan \in [val : Data,  rdy : {0, 1},  ack : {0, 1}]
-----------------------------------------------------------------------
Init  ==  /\ TypeInvariant
          /\ chan.ack = chan.rdy 
          /\ HCini

Send(d) ==  /\ chan.rdy = chan.ack
            /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv     ==  /\ chan.rdy # chan.ack
            /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next  ==  Send(hr) \/ Rcv

Spec  ==  Init /\ [][Next /\ HCnxt]_{chan, hr}
-----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=======================================================================
