# Partition transfers and finite lattice ideals

## Abstract

Native partition transfers are one-cell exchanges of finite Young ideals in the integer lattice.

The vertices are native Nat.Partition values, with multiplicities retained. Their Young diagrams are finite lower ideals in the nonnegative integer lattice. An edge exchanges exactly one cell; the multiset description also permits a virtual zero recipient and omits zero remainders.

**Definition 1.1 (A row with zero omitted).**

$$\forall k \in Nat,\; \operatorname{part}\left(k\right) = \operatorname{positiveSingleton}\left(k\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.part` (`✓ std3`).

*Citation.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

positiveSingleton(k) is empty at zero and contains one occurrence of k otherwise.

**Definition 1.2 (Two distinct occurrences).**

$$\forall n \in Nat,\; \forall p \in \operatorname{Partition}\left(n\right),\; \forall q \in \operatorname{Partition}\left(n\right),\; \operatorname{UnitTransfer}\left(p, q\right) \Leftrightarrow \left(p \ne q \land \left(\exists s \in \operatorname{Multiset}\left(Nat\right),\; \exists a \in Nat,\; \exists b \in Nat,\; \operatorname{parts}\left(p\right) = \operatorname{singleton}\left(a + 1\right) + \operatorname{part}\left(b\right) + s \land \operatorname{parts}\left(q\right) = \operatorname{part}\left(a\right) + \operatorname{singleton}\left(b + 1\right) + s\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.UnitTransfer` (`✓ std3`).

*Citation.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

The a+1 donor and b recipient are two slots in the multiset decomposition. Thus equal positive sizes require two occurrences; b=0 creates a new part, and a=0 deletes the donor remainder. The residual multiset s retains every unaffected occurrence.

**Definition 1.3 (The literal partition graph).**

$$\forall n \in Nat,\; \forall p \in \operatorname{Partition}\left(n\right),\; \forall q \in \operatorname{Partition}\left(n\right),\; \operatorname{Adj}\left(\operatorname{graph}\left(n\right), p, q\right) \Leftrightarrow \operatorname{UnitTransfer}\left(p, q\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.graph` (`✓ std3`).

*Citation.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

Reversing the two slots reverses a transfer. Self-results are excluded, so this is a simple graph.

**Theorem 1.4 (Sum of a row occurrence).**

$$\forall k \in Nat,\; \operatorname{sum}\left(\operatorname{part}\left(k\right)\right) = k$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.part_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

Omitting a zero row preserves its sum. The staircase-cardinality proof consumes this helper.

**Theorem 1.5 (Partitions determined by their diagrams).**

$$\forall n \in Nat,\; \operatorname{Injective}\left(\operatorname{ofPartitionOn}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.diagram_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

ofPartitionOn(n) maps each native partition of n to its Young diagram. This is the injectivity inherited from Mathlib's partition/diagram equivalence; the star, top and first-family proofs consume it.

**Theorem 1.6 (Rows reconstruct the partition multiset).**

$$\forall d \in YoungDiagram,\; \forall H \in Nat,\; \operatorname{colLen}\left(d, 0\right) \le H \Rightarrow \operatorname{sumPositiveRows}\left(d, H\right) = \operatorname{rowLens}\left(d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.row_parts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

sumPositiveRows(d,H) is the multiset sum of part(rowLen(d,i)) for i in range(H). Rows beyond the diagram's height are zero and contribute no occurrence. Row decompositions in the converse transfer proof and the staircase-cardinality proof consume this identity.

**Theorem 1.7 (Transfers and diagram intersections).**

$$\forall n \in Nat,\; \forall p \in \operatorname{Partition}\left(n\right),\; \forall q \in \operatorname{Partition}\left(n\right),\; 0 < n \Rightarrow \left(\operatorname{UnitTransfer}\left(p, q\right) \Leftrightarrow \operatorname{card}\left(\operatorname{inf}\left(\operatorname{ofPartition}\left(p\right), \operatorname{ofPartition}\left(q\right)\right)\right) = n - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.transfer_iff_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fedor B. Lyudogovskiy (2026). *Simplex Stratification and Phase Boundaries in the Partition Graph*. URL: <https://arxiv.org/html/2603.23228v1>.

*Commentary.*

A transfer has a common size-(n-1) predecessor: shrink the donor before increasing the recipient. Column counts show inclusion after sorting, including repeated sizes. Conversely the two singleton cell differences lie in distinct rows. Decomposing the row multisets at those indices yields the donor and recipient slots, with zero rows omitted. This bridge does not itself establish either full-question proposition.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.UnitTransfer`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.diagram_injective`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.graph`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.part`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.part_sum`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.row_parts`
- Truth anchor: `D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.transfer_iff_intersection`
- Dependency: [D5/S1/Words/Compositions/StrictFirstSumsGapfreeOddParts](../../../S1/Words/Compositions/StrictFirstSumsGapfreeOddParts.md)
