---- MODULE HourClock ----
EXTENDS Naturals
----
Inner(hr) == INSTANCE InnerHourClock
Spec == \EE hr : Inner(hr)!HC
====
