# Finite Additive Readout Blocks

## Abstract

Finite additive readouts of one coherent source determine quotient blocks and flat marginals.

The source G and label spaces A and B are finite additive commutative groups. The maps alpha and beta are additive homomorphisms from that same source, and the paired map is injective. Blocks are indexed by G modulo the sum of the two kernels. Source amplitudes are divided by the square root of the source cardinality; labels outside a readout image have zero amplitude.

**Theorem 1.1 (Paired block criterion).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.paired_block_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.paired_block_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pair of readout labels comes from one source element exactly when the two labels occur in the same quotient block. The kernel sum lets representatives on the two sides be joined into one source. This criterion itself requires neither finiteness nor joint injectivity.

**Theorem 1.2 (Actual coefficient blocks).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.actual_coefficient_block`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.actual_coefficient_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a jointly injective pair of readouts, each coefficient of the actual source sum is the normalized indicator of its unique quotient block. The assertion comes from the source sum, rather than a prescribed block matrix.

**Theorem 1.3 (Right block cardinality).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.right_block_card`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.right_block_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each right block has as many distinct labels as the left readout kernel has elements. Joint injectivity gives the needed bijection.

**Theorem 1.4 (Source cosets and product blocks).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.source_coset_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.source_coset_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The paired readout restricts to a bijection from each source coset onto the product of its left and right label blocks. Both coordinates of the bijection are the original readout values.

**Theorem 1.5 (Matrices from the actual source).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.actual_block_matrices`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.actual_block_matrices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalized left and right block columns are orthonormal. The actual coefficient matrix factors through these columns with the square-root block weight. Taking its two actual partial traces gives scaled block projections, their column actions, and zero action on the respective conjugate-transpose kernels. Both block projections are Hermitian and idempotent. The blocks on each side are disjoint and their union is precisely that readout's image. Left and right blocks have the respective opposite kernel cardinalities. For every chosen representative, their labels are its readout translated by the opposite kernel image. Both reductions square to the block weight times themselves. Their entries are the same-block indicators summed over the quotient and scaled by the corresponding kernel cardinality divided by the source cardinality. The quotient cardinality is bounded by both ambient label cardinalities.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.actual_block_matrices`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.actual_coefficient_block`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.paired_block_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.right_block_card`
- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.source_coset_product`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Sharpness/FreeNegentropyBudget](../Sharpness/FreeNegentropyBudget.md)
