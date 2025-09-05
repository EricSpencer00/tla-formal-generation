---- MODULE {{module}} ----
EXTENDS Naturals, Sequences, TLC
VARIABLES {{vars}}

Init == TRUE
Next == UNCHANGED {{vars}}

{{invariant}}

====
