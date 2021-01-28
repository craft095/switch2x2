------ MODULE OriginalSwitch2x2 ------

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

The Original Switch is an extension of the Simplified Switch. The Original switch
contains an additional counter, that counts interesting packets that are transferred
from input to output buffers. A packet is considered interesting if its
second, third, and fourth bit are all 0. The counter is restricted. Therefore the
value can only be incremented by one per clock cycle. So when both input buffers
are capable of transferring interesting packets, priority is given to the transferral
of packets from input buffer 0 and the transferral of packets from input buffer
1 is delayed. Thus, we may only transfer packets simultaneously if they are not
both interesting. In all other cases a process needs to either take or grant priority
as in the Simplified Switch case study.
*)

EXTENDS Sequences, Naturals

CONSTANTS MaxSize, Bit0, Bit1, Interesting, NotInteresting

VARIABLES queueIn0, opIn0
VARIABLES queueIn1, opIn1
VARIABLES queueOut0, opOut0
VARIABLES queueOut1, opOut1
VARIABLES counter \* To count inetersting packets

Packets == { Bit0, Bit1 } \X { Interesting, NotInteresting }

HasBit0(p) == p[1] = Bit0
HasBit1(p) == p[1] = Bit1

IsInteresting(p) == p[2] = Interesting

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

vars == <<queueIn0, opIn0, queueIn1, opIn1, queueOut0, opOut0, queueOut1, opOut1, counter>>

\* Inherit type invariants from the Queue
TypeOk ==
    /\ In0!TypeOk /\ In1!TypeOk /\ Out0!TypeOk /\ Out1!TypeOk
    \* As we never intersted in this value per se, we model it as alternating value
    /\ counter \in BOOLEAN

\* All queues are empty at the beginning
Init ==
    /\ In0!Init /\ In1!Init /\ Out0!Init /\ Out1!Init
    /\ queueIn0 = <<>> /\ queueIn1 = <<>> /\ queueOut0 = <<>> /\ queueOut1 = <<>>
    /\ counter = TRUE

\* If both input queues want to write to the same queue _or_ both queues have interesting packets
Conflict ==
    /\ queueIn0 /= <<>>
    /\ queueIn1 /= <<>>
    /\
        \/ \* Both inputs wants to write to output 0
            /\ HasBit0(Head(queueIn0))
            /\ HasBit0(Head(queueIn1))
            /\ Len(queueOut0) < MaxSize
        \/ \* Both inputs wants to write to output 1
            /\ HasBit1(Head(queueIn0))
            /\ HasBit1(Head(queueIn1))
            /\ Len(queueOut1) < MaxSize
        \/ \* Both inputs have interesting packets
            /\ IsInteresting(Head(queueIn0))
            /\ IsInteresting(Head(queueIn1))
            /\ HasBit0(Head(queueIn0)) /= HasBit0(Head(queueIn1))
            /\ Len(queueOut0) < MaxSize
            /\ Len(queueOut1) < MaxSize

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

IsInterestingTransfered ==
    \/ (In0Out0 \/ In0Out1) /\ IsInteresting(Head(queueIn0))
    \/ (In1Out0 \/ In1Out1) /\ IsInteresting(Head(queueIn1))

IncCounter == counter' = ~counter

Tick == /\ Transfer
        /\ IsInterestingTransfered => IncCounter
        /\ ~IsInterestingTransfered => UNCHANGED counter
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
        /\ HasBit0(Head(queueIn1)) = HasBit0(Head(queueIn0))
    \/ \* input 0 has priority over input 1
        /\ queueIn0 /= <<>>
        /\ queueIn1 /= <<>>
        /\ IsInteresting(Head(queueIn1)) /\ IsInteresting(Head(queueIn0))

TransferOut0 == Out0!Get =>
    \/ Len(queueOut0) = MaxSize
    \/
        /\
            \/ queueIn0 = <<>>
            \/ queueIn0 /= <<>> /\ ~HasBit0(Head(queueIn0))
        /\
            \/ queueIn1 = <<>>
            \/ queueIn1 /= <<>> /\ ~HasBit0(Head(queueIn1))
    \/ \* two interesting packets and both could be sent into different queues
            \* high priority input 0 wants to write to output1
            /\ queueIn0 /= <<>> /\ ~HasBit0(Head(queueIn0))
            \* low priority input 1 wants to write to output0
            /\ queueIn1 /= <<>> /\ HasBit0(Head(queueIn1))
            \* high priority input 0 is not blocked by output 1
            /\ Len(queueOut1) /= MaxSize
            \* both inputs have interesting packets
            /\ IsInteresting(Head(queueIn0)) /\ IsInteresting(Head(queueIn1))

TransferOut1 == Out1!Get =>
    \/ Len(queueOut1) = MaxSize
    \/
        /\
            \/ queueIn0 = <<>>
            \/ queueIn0 /= <<>> /\ ~HasBit1(Head(queueIn0))
        /\
            \/ queueIn1 = <<>>
            \/ queueIn1 /= <<>> /\ ~HasBit1(Head(queueIn1))
    \/ \* two interesting packets and both could be sent into different queues
            \* high priority input 0 wants to write to output0
            /\ queueIn0 /= <<>> /\ ~HasBit1(Head(queueIn0))
            \* low priority input 1 wants to write to output1
            /\ queueIn1 /= <<>> /\ HasBit1(Head(queueIn1))
            \* high priority input 0 is not blocked by output 0
            /\ Len(queueOut0) /= MaxSize
            \* both inputs have interesting packets
            /\ IsInteresting(Head(queueIn0)) /\ IsInteresting(Head(queueIn1))

TransferIn0P == [] [TransferIn0]_vars
TransferIn1P == [] [TransferIn1]_vars
TransferOut0P == [] [TransferOut0]_vars
TransferOut1P == [] [TransferOut1]_vars

\* If there are data and no conflict, simultanious transfer must occur
MaxThroughput ==
    (
        /\ ~Conflict
        /\ queueIn0 /= <<>>
        /\ queueIn1 /= <<>>
        /\ Len(queueOut0) /= MaxSize
        /\ Len(queueOut1) /= MaxSize
    ) =>
        /\ In0!Get \* Transfer from queue in 0
        /\ In1!Get \* Transfer from queue in 1

MaxThroughputP == [] [MaxThroughput]_vars

=============================================================================
