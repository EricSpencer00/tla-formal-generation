---- MODULE SimpleCounter ----
EXTENDS Naturals, TLC
CONSTANT Max
VARIABLES counter

Init == counter = 0

Inc == (counter < Max) /\ counter' = counter + 1
Dec == (counter > 0) /\ counter' = counter - 1

Next == Inc \/ Dec

Inv == counter >= 0

====
