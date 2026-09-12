# Finite Padding Memory

## Abstract

Exact finite padding memory and transition coordinates.

For a finite index type I and a capacity function c:I to Nat, TailBox(c) contains bounded tail coordinates. PositiveTail(c) removes the all-zero tail, and PaddingMemory(H,c)=Option(PositiveTail(c) x Fin(H+1)) is the finite memory used by the padding construction.

**Theorem 1.1 (The padding memory has exact cardinality).**

$$\forall I \in Type,\; Fintype\left(I\right) \Rightarrow \left(\forall H \in \mathbb{N},\; \forall c \in Function\left(I, \mathbb{N}\right),\; card\left(PaddingMemory\left(H, c\right)\right) = \left(H + 1\right) \cdot \prod_{i:I}{c\left(i\right) + 1} - H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingMemory.padding_memory_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing the all-zero tail and adjoining the None sink gives the displayed product-minus-H count.

**Theorem 1.2 (Occupation memory has product-minus-head cardinality).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall q \in A,\; card\left(OccupationMemory\left(a, q\right)\right) = \prod_{i:A}{count\left(a, i\right) + 1} - count\left(a, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingMemory.occupation_memory_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choosing a letter of maximum count makes this count the product minus the maximum. The sink exists even when every count is zero.

**Theorem 1.3 (A head of maximum count exists).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \exists q \in A,\; count\left(a, q\right) = maxCount\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingMemory.maximal_head_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonempty A, maxCount(a) is the supremum over all i:A of count(a,i). The exact memory equivalence uses this equality to label the memory by Fin of the product-minus-maximum dimension.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingMemory.maximal_head_exists`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingMemory.occupation_memory_card`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingMemory.padding_memory_card`
- Dependency: [D5/S3/Quantum/Entanglement/OccupancyWordSectors](../Entanglement/OccupancyWordSectors.md)
- Dependency: [D5/S3/Quantum/Entanglement/SequentialRegisterCircuit](../Entanglement/SequentialRegisterCircuit.md)
