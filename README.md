# Switch 2x2 Specification

I was interested in comparison of TLA+ with other formalisms [1].

There are three specifications I would like to design with TLA+ to verify claims from the article:

- Simplified switch
- Original switch
- Modified switch

All the text specs below are copy pasted from [1]. All the TLA+ specs are mine.

I use `*.model` files to configure TLC using my own utility [2]. This tool produces necessary files
to run TLC (these files are also in the repo).

## Simplified Switch 2x2

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

## Original Switch 2x2

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

## Modified Switch 2x2

The modified 2 × 2 switch alters the way the priority is handled amongst colliding
transfers in the case that the packets are both interesting and have a different
destination. We have defined two conditions, namely both head packets have the
same destination (C1) and both head packets are interesting (C2). If either one
of these conditions holds, priority is given to the transferral of the packet from
input buffer 0.
Now, in the Modified Switch, we keep that if C1 holds, the first input buffer
will be given priority over the second buffer. However if C1 does not hold, while
C2 holds, priority is given to transferral of the packet from input buffer 1.

## References

 [1] https://link.springer.com/chapter/10.1007%2F978-3-642-17071-3_9
 [2] https://github.com/craft095/tlamodel
