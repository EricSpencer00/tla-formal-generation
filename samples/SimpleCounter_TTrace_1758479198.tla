---- MODULE SimpleCounter_TTrace_1758479198 ----
EXTENDS Sequences, TLCExt, SimpleCounter, Toolbox, Naturals, TLC

_expression ==
    LET SimpleCounter_TEExpression == INSTANCE SimpleCounter_TEExpression
    IN SimpleCounter_TEExpression!expression
----

_trace ==
    LET SimpleCounter_TETrace == INSTANCE SimpleCounter_TETrace
    IN SimpleCounter_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        counter = (-1)
    )
----

_init ==
    /\ counter = _TETrace[1].counter
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ counter  = _TETrace[i].counter
        /\ counter' = _TETrace[j].counter

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("SimpleCounter_TTrace_1758479198.json", _TETrace)

=============================================================================

 Note that you can extract this module `SimpleCounter_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `SimpleCounter_TEExpression.tla` file takes precedence 
  over the module `SimpleCounter_TEExpression` below).

---- MODULE SimpleCounter_TEExpression ----
EXTENDS Sequences, TLCExt, SimpleCounter, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `SimpleCounter` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        counter |-> counter
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_counterUnchanged |-> counter = counter'
        
        \* Format the `counter` variable as Json value.
        \* ,_counterJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(counter)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_counterModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].counter # _TETrace[s-1].counter
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE SimpleCounter_TETrace ----
\*EXTENDS IOUtils, SimpleCounter, TLC
\*
\*trace == IODeserialize("SimpleCounter_TTrace_1758479198.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE SimpleCounter_TETrace ----
EXTENDS SimpleCounter, TLC

trace == 
    <<
    ([counter |-> 0]),
    ([counter |-> -1])
    >>
----


=============================================================================

---- CONFIG SimpleCounter_TTrace_1758479198 ----

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Sun Sep 21 13:26:38 CDT 2025