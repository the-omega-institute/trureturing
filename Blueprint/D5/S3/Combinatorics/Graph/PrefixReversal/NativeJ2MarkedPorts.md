# Actual Native J2 Marked Ports

## Abstract

The twelve independently defined native J2 ports are distinct, and the six actual marked b cuts have disjoint endpoints.

A port is indexed by i in Fin(3), a Boolean exchanging the actual values p=0 and q=m, and a Boolean choosing the left side. Right ports are the independently defined R0=(q,p,A,v), R1=(p,A,q,v), R2=(A,q,p,v), with A=(1,...,m-2) and v=m-1. Left ports multiply the corresponding right port by the actual length-m reversal b. The label exchange acts by left multiplication, so it commutes with every reversal of positions.

**Theorem 1.1 (Twelve Distinct Actual Vertices).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \mathrm{Injective}\left(\mathrm{port}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts.native_j2_port_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five, port(m) is injective on Fin(3) times Bool times Bool. The proof compares actual permutation values at positions 0, 1, 2 and m-1. These coordinates distinguish every possible pair, including the opposite orientations of A.

**Theorem 1.2 (The Common Actual Terminal Label).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall p \in \mathrm{Prod}\left(\mathrm{Fin}\left(3\right), \mathrm{Prod}\left(\mathrm{Bool}, \mathrm{Bool}\right)\right),\; \mathrm{val}\left(\mathrm{apply}\left(\mathrm{port}\left(m, p\right), \mathrm{last}\left(m\right)\right)\right) = \mathrm{sub}\left(m, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts.native_j2_port_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five, every port has actual terminal value m-1. This follows from the native reversal, rotation and label-swap formulas, rather than an assumed tuple interpretation.

**Theorem 1.3 (Actual Generator Edges).**

$$\forall m \in \mathrm{Nat},\; \forall p \in \mathrm{Prod}\left(\mathrm{Fin}\left(3\right), \mathrm{Bool}\right),\; \mathrm{markedEdge}\left(m, p\right) = \mathrm{symPair}\left(\mathrm{port}\left(m, \mathrm{tuple}\left(\mathrm{fst}\left(p\right), \mathrm{snd}\left(p\right), \mathrm{false}\right)\right), \mathrm{mul}\left(\mathrm{port}\left(m, \mathrm{tuple}\left(\mathrm{fst}\left(p\right), \mathrm{snd}\left(p\right), \mathrm{false}\right)\right), \mathrm{b}\left(m\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts.native_j2_marked_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each marked pair is exactly the undirected b-generator edge from its right port. This identity holds at every size; the left/right correspondence is part of the actual permutation definitions.

**Theorem 1.4 (Disjoint Endpoints of the Six Cuts).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall p \in \mathrm{Prod}\left(\mathrm{Fin}\left(3\right), \mathrm{Bool}\right),\; \forall q \in \mathrm{Prod}\left(\mathrm{Fin}\left(3\right), \mathrm{Bool}\right),\; p \ne q \Rightarrow \mathrm{Disjoint}\left(\mathrm{endpoints}\left(\mathrm{markedEdge}\left(m, p\right)\right), \mathrm{endpoints}\left(\mathrm{markedEdge}\left(m, q\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts.native_j2_marked_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five, two different indices in Fin(3) times Bool give cuts with no endpoint in common. A shared actual endpoint would contradict the proved twelve-port injection.

These results prove the actual marked-cut geometry. Membership of the cuts in one particular F2 Hamilton witness, legality of the five literal J2 words, exhaustion of path components and all-size Hamiltonicity require separate proofs.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts.native_j2_marked_disjoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts.native_j2_marked_edge`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts.native_j2_port_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts.native_j2_port_last`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Words](NativeJ2Words.md)
