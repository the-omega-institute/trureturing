# Opposite Native Marked Ports

## Abstract

Canonical protected-label exchange separates the complete native rotation and reversal port tables. The separation is earned from two adjacent independent base positions, not supplied as a recursive-state hypothesis.

**Theorem 1.1 (All Four Native Port Intersections Are Empty).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \left(\mathrm{AtLeast}\left(k, 2\right) \land \mathrm{AtLeast}\left(\mathrm{Length}\left(\mathrm{Base}\left(frame\right)\right), 3\right)\right) \Rightarrow \left(\forall i \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; \left(\mathrm{RightPort}\left(\mathrm{OppositeSelectedFrame}\left(frame\right), j\right) = \mathrm{RightPort}\left(frame, i\right) \Rightarrow \mathrm{False}\right) \land \left(\left(\mathrm{RightPort}\left(\mathrm{OppositeSelectedFrame}\left(frame\right), j\right) = \mathrm{LeftPort}\left(frame, i\right) \Rightarrow \mathrm{False}\right) \land \left(\left(\mathrm{LeftPort}\left(\mathrm{OppositeSelectedFrame}\left(frame\right), j\right) = \mathrm{RightPort}\left(frame, i\right) \Rightarrow \mathrm{False}\right) \land \left(\mathrm{LeftPort}\left(\mathrm{OppositeSelectedFrame}\left(frame\right), j\right) = \mathrm{LeftPort}\left(frame, i\right) \Rightarrow \mathrm{False}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeMarkedPorts.native_opposite_ports_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complete frame with at least two selected labels and at least three independent base labels, every natural rotation index i and j gives four unequal native configurations: opposite right versus original right or left, and opposite left versus original right or left. The opposite frame exchanges exactly the protected final selected pair. Its anchor is the protected-label transposition multiplied by the original anchor. This transposition fixes the labels at adjacent base positions k and k plus one. One fixed prefix position forces an intersecting pair of rotations to have identical rotation permutations, contradicting the nontrivial transposition. Two adjacent fixed positions would force an intersecting rotation and reflection to satisfy zero congruent to two modulo m, contradicting m at least five. No Hamiltonian-cycle witness or all-order recursive existence is assumed or asserted.

**Theorem 1.2 (Both Marked Tables Jointly Have Unique Vertices).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \left(\mathrm{AtLeast}\left(k, 2\right) \land \mathrm{AtLeast}\left(\mathrm{Length}\left(\mathrm{Base}\left(frame\right)\right), 3\right)\right) \Rightarrow \mathrm{Injective}\left(\mathrm{TaggedSpecialPort}\left(frame, \mathrm{OppositeSelectedFrame}\left(frame\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeMarkedPorts.native_opposite_marked_port_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same explicit selected-count and base-length assumptions, the function indexed by a Boolean order tag and a pair from Fin(k plus one) times Fin(two) is injective. Each tag selects the original frame or its canonical protected-label exchange. Within either table the existing native special-port injection applies; between the tables the newly earned four-way separation applies. Distinct tags therefore cannot silently refer to the same actual native vertex.

**Theorem 1.3 (The Two Actual Marked Deletion Sets Are Disjoint).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \left(\mathrm{AtLeast}\left(k, 2\right) \land \mathrm{AtLeast}\left(\mathrm{Length}\left(\mathrm{Base}\left(frame\right)\right), 3\right)\right) \Rightarrow \mathrm{Disjoint}\left(\mathrm{MarkedCuts}\left(frame\right), \mathrm{MarkedCuts}\left(\mathrm{OppositeSelectedFrame}\left(frame\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeMarkedPorts.native_opposite_marked_cuts_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under those same assumptions, markedCuts of the original frame and markedCuts of its canonical opposite frame have no common undirected edge. Every marked cut joins its literal right and left ports at one index. Equality of two undirected edges would identify the opposite right port with one original endpoint, contradicting the earned separation. This supplies an actual deletion-set invariant for simultaneous path partitions; it does not build those partitions or their common cycle witness.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeMarkedPorts.native_opposite_marked_cuts_disjoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeMarkedPorts.native_opposite_marked_port_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeMarkedPorts.native_opposite_ports_disjoint`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJointMarkedCutShift](NativeJointMarkedCutShift.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders](NativeOppositeSelectedOrders.md)
