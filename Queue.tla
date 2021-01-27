----- MODULE Queue -----

EXTENDS Sequences, Naturals

CONSTANTS Tags, MaxSize

VARIABLES queue, op

vars == <<queue, op>>

OpNames == { "init", "put", "get" }

TypeOk ==
    /\ \E n \in 0..MaxSize : queue \in [1..n -> Tags]
    /\ op \in (OpNames \X Tags \X BOOLEAN)

Init ==
    /\ \E n \in 0..MaxSize : queue \in [1..n -> Tags]
    /\ op = <<"init", CHOOSE x \in Tags : TRUE, TRUE>>

PutValue(t) ==
    /\ Len(queue) < MaxSize
    /\ op' = <<"put", t, ~op[3]>>
    /\ queue' = Append(queue, t)

Put == \E t \in Tags : PutValue(t)

Get ==
    /\ Len(queue) > 0
    /\ op' = <<"get", Head(queue), ~op[3]>>
    /\ queue' = Tail(queue)

Next == Put \/ Get

Spec == Init /\ [][Next]_vars

=============================================================================
