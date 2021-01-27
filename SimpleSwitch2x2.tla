------ MODULE SimpleSwitch2x2 ------

(*
Taken from: https://link.springer.com/chapter/10.1007%2F978-3-642-17071-3_9

The Simplified Switch contains two input FIFO buffers and two output FIFO
buffers. All buffers have a unique identity, w.r.t. the type of buffer, e.g. each
input or output buffer corresponds to a numerical value, and a finite capacity
for storing packets. All buffers have the same capacity.
Each packet consists of 32 bits. Packets enter the system via the input buffers
and depart the system via the output buffers. Packets are transferred from an
input buffer to one of the output buffers based on the first bit of the packet: If
the first bit of a packet is 0, it is routed to the output buffer with identity 0,
and otherwise it is routed to the output buffer with identity 1.
The packets may only be transferred if the relevant output buffer is not full.
A buffer operates per clock cycle and can do at most one operation, namely
receive a packet, send a packet, or nothing. Furthermore, we require maximum
throughput, e.g. a packet should be transferred if it has the ability to. Next to
that, if packets from different input buffers are available for transferral to the
same output buffer, transferral of the packet from input buffer 0 gets priority
over transferral of the packet from input buffer 1.
*)

EXTENDS Sequences, Naturals

CONSTANTS MaxSize

VARIABLES queueIn0, opIn0
VARIABLES queueIn1, opIn1
VARIABLES queueOut0, opOut0
VARIABLES queueOut1, opOut1

\* The only interesting part of the content of the packets is the first bit. So we can model packets
\* as { 0, 1 }
Packets == { 0, 1 }

HasBit0(p) == p = 0
HasBit1(p) == p = 1

\* Input queues
In0 == INSTANCE Queue WITH
    queue <- queueIn0, op <- opIn0, Tags <- Packets
In1 == INSTANCE Queue WITH
    queue <- queueIn1, op <- opIn1, Tags <- Packets

\* Output queues
Out0 == INSTANCE Queue WITH
    queue <- queueOut0, op <- opOut0, Tags <- Packets
Out1 == INSTANCE Queue WITH
    queue <- queueOut1, op <- opOut1, Tags <- Packets

vars == <<queueIn0, opIn0, queueIn1, opIn1, queueOut0, opOut0, queueOut1, opOut1>>

\* Inherit type invariants from the Queue
TypeOk ==
    /\ In0!TypeOk /\ In1!TypeOk /\ Out0!TypeOk /\ Out1!TypeOk

\* All queues are empty at the beginning
Init ==
    /\ In0!Init /\ In1!Init /\ Out0!Init /\ Out1!Init
    /\ queueIn0 = <<>> /\ queueIn1 = <<>> /\ queueOut0 = <<>> /\ queueOut1 = <<>>

\* If both input queues want to write to the same queue
Conflict ==
    /\ queueIn0 /= <<>>
    /\ queueIn1 /= <<>>
    /\ Head(queueIn0) = Head(queueIn1)

\* Transfer from high priority input 0 to outputs
In0Out0 ==
    /\ queueIn0 /= <<>>
    /\ HasBit0(Head(queueIn0))
    /\ Len(queueOut0) < MaxSize
In0Out1 ==
    /\ queueIn0 /= <<>>
    /\ HasBit1(Head(queueIn0))
    /\ Len(queueOut1) < MaxSize

\* Use input 1 only if there is no pending packet in input 0 to the same output
In1Out0 ==
    /\ ~Conflict
    /\ queueIn1 /= <<>>
    /\ HasBit0(Head(queueIn1))
    /\ Len(queueOut0) < MaxSize
In1Out1 ==
    /\ ~Conflict
    /\ queueIn1 /= <<>>
    /\ HasBit1(Head(queueIn1))
    /\ Len(queueOut1) < MaxSize

Transfer ==
    /\ In0Out0 => (In0!Get /\ Out0!PutValue(Head(queueIn0)))
    /\ In0Out1 => (In0!Get /\ Out1!PutValue(Head(queueIn0)))
    /\ In1Out0 => (In1!Get /\ Out0!PutValue(Head(queueIn1)))
    /\ In1Out1 => (In1!Get /\ Out1!PutValue(Head(queueIn1)))

Tick == /\ Transfer
        \* Transfer has priority over other operations
        /\ (~In0Out0 /\ ~In0Out1) => (In0!Put \/ UNCHANGED <<queueIn0, opIn0>>)
        /\ (~In1Out0 /\ ~In1Out1) => (In1!Put \/ UNCHANGED <<queueIn1, opIn1>>)
        /\ (~In0Out0 /\ ~In1Out0) => (Out0!Get \/ UNCHANGED <<queueOut0, opOut0>>)
        /\ (~In0Out1 /\ ~In1Out1) => (Out1!Get \/ UNCHANGED <<queueOut1, opOut1>>)

Next == Tick

Spec == Init /\ [][Next]_vars

\* Queue refinements
SpecIn0 == In0!Spec
SpecIn1 == In1!Spec
SpecOut0 == Out0!Spec
SpecOut1 == Out1!Spec

\* Output 0 can only contain `zero` packets
Out0ZeroOnly == \A i \in DOMAIN queueOut0 : HasBit0(queueOut0[i])

\* Output 1 can only contain `one` packets
Out1OneOnly == \A i \in DOMAIN queueOut1 : HasBit1(queueOut1[i])

\* Eager transfer: only put something into input if no transfer possible
TransferIn0 == In0!Put =>
    \/ queueIn0 = <<>>
    \/
        /\ HasBit0(Head(queueIn0))
        /\ Len(queueOut0) = MaxSize
    \/
        /\ HasBit1(Head(queueIn0))
        /\ Len(queueOut1) = MaxSize

TransferIn1 == In1!Put =>
    \/ queueIn1 = <<>>
    \/
        /\ queueIn1 /= <<>>
        /\ HasBit0(Head(queueIn1))
        /\ Len(queueOut0) = MaxSize
    \/
        /\ queueIn1 /= <<>>
        /\ HasBit1(Head(queueIn1))
        /\ Len(queueOut1) = MaxSize
    \/ \* input 0 has priority over input 1
        /\ queueIn0 /= <<>>
        /\ queueIn1 /= <<>>
        /\ Head(queueIn1) = Head(queueIn0)

TransferOut0 == Out0!Get =>
    \/ Len(queueOut0) = MaxSize
    \/
        /\
            \/ queueIn0 = <<>>
            \/ queueIn0 /= <<>> /\ ~HasBit0(Head(queueIn0))
        /\
            \/ queueIn1 = <<>>
            \/ queueIn1 /= <<>> /\ ~HasBit0(Head(queueIn1))

TransferOut1 == Out1!Get =>
    \/ Len(queueOut1) = MaxSize
    \/
        /\
            \/ queueIn0 = <<>>
            \/ queueIn0 /= <<>> /\ ~HasBit1(Head(queueIn0))
        /\
            \/ queueIn1 = <<>>
            \/ queueIn1 /= <<>> /\ ~HasBit1(Head(queueIn1))

TransferIn0P == [] [TransferIn0]_vars
TransferIn1P == [] [TransferIn1]_vars
TransferOut0P == [] [TransferOut0]_vars
TransferOut1P == [] [TransferOut1]_vars

=============================================================================
