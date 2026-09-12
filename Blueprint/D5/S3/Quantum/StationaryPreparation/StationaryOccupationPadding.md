# Stationary Occupation Padding

## Abstract

Finite padding isometries and the physical stationary occupation gate.

For a finite tail alphabet I and natural capacities c, PaddingMemory(H,c) consists of a sink and pairs of a nonzero bounded tail with a head index in Fin(H+1). Each legal emission has the square root of its probability as its amplitude. The matrix maps each memory basis vector into the joint letter and memory space. Here coefficient(U,v,p)=(U v)(p) denotes the p coordinate of U(v).

**Theorem 1.1 (Padding transition probabilities sum to one).**

$$\forall I \in Type,\; \left(Fintype\left(I\right) \land DecidableEq\left(I\right)\right) \Rightarrow \left(\forall H \in \mathbb{N},\; \forall c \in Function\left(I, \mathbb{N}\right),\; \forall s \in PaddingMemory\left(H, c\right),\; \sum_{i:Option\left(I\right)}{paddingProbability\left(H, c, s, i\right)} = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding.padding_probability_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sink, head predecessor and positive tail predecessors partition the legal emissions, including the one-tail boundary.

**Theorem 1.2 (The padding matrix has orthonormal columns).**

$$\forall I \in Type,\; \left(Fintype\left(I\right) \land DecidableEq\left(I\right)\right) \Rightarrow \left(\forall H \in \mathbb{N},\; \forall c \in Function\left(I, \mathbb{N}\right),\; conjTranspose\left(paddingMatrix\left(H, c\right)\right) \cdot paddingMatrix\left(H, c\right) = identity\left(PaddingMemory\left(H, c\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding.padding_matrix_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct predecessor states have disjoint legal emissions in the (letter, memory) output space, and the probability identity gives unit column norm.

**Theorem 1.3 (The padding matrix is realized by one unitary).**

$$\forall I \in Type,\; \left(Fintype\left(I\right) \land DecidableEq\left(I\right)\right) \Rightarrow \left(\forall H \in \mathbb{N},\; \forall c \in Function\left(I, \mathbb{N}\right),\; \exists U \in Unitary\left(Prod\left(Option\left(I\right), PaddingMemory\left(H, c\right)\right)\right),\; \forall j \in PaddingMemory\left(H, c\right),\; \forall i \in Option\left(I\right),\; \forall k \in PaddingMemory\left(H, c\right),\; coefficient\left(U, basis\left(pair\left(none\left(\right), j\right)\right), pair\left(i, k\right)\right) = paddingMatrix\left(H, c, pair\left(i, k\right), j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding.padding_unitary_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite isometry extends to a unitary while preserving every displayed matrix coefficient.

**Theorem 1.4 (The physical matrix is an isometry).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; conjTranspose\left(physicalMatrix\left(a\right)\right) \cdot physicalMatrix\left(a\right) = identity\left(Fin\left(proposedDimension\left(a\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding.physical_matrix_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite-index relabeling transports the padding Gram identity to physical memory coordinates.

**Theorem 1.5 (The physical sink vector is normalized).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; norm\left(physicalFinal\left(a\right)\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding.physical_final_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The final vector is the basis vector at the transported sink state.

**Theorem 1.6 (Physical gate coefficients equal matrix entries).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land \left(DecidableEq\left(A\right) \land Nonempty\left(A\right)\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall j \in Fin\left(proposedDimension\left(a\right)\right),\; \forall i \in A,\; \forall k \in Fin\left(proposedDimension\left(a\right)\right),\; coefficient\left(physicalGate\left(a\right), basis\left(pair\left(maximalHead\left(a\right), j\right)\right), pair\left(i, k\right)\right) = physicalMatrix\left(a, pair\left(i, k\right), j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding.physical_gate_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relabeled unitary exposes the exact weighted transition coefficient used by the residual circuit.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding.padding_matrix_gram`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding.padding_probability_sum`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding.padding_unitary_exists`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding.physical_final_norm`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding.physical_gate_coefficients`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding.physical_matrix_gram`
- Dependency: [D5/S3/Quantum/StationaryPreparation/PaddingMemory](PaddingMemory.md)
