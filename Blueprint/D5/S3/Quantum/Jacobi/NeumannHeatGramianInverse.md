# The sharp finite Gramian jet of a positive Neumann path

## Abstract

Sparse coefficients of the centered heat Gramian identify a positive ordered path of known total length. Exchanging the final two unequal edges shows the least degree needed in a full jet.

**Theorem 1.1 (The cubic coefficient of the centered physical Gramian).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.cubic_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.cubic_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive path with at least one edge, write a for the length of its first edge. The Gramian coefficients of degrees zero, one, and two vanish. The coefficient of degree three is 4/(3a^6) for every additive constant in the heat response.

In the formal variance the constant and quadratic heat coefficients cancel from the cubic term. The remaining term is the square of the linear heat coefficient divided by twelve. The lumped endpoint mass is a/2, so the first physical moment is 4/a^3.

**Definition 1.2 (Degree of the readout at each edge).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.readoutDegree`

*Formalization.* `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.readoutDegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For edges indexed from zero at the measured endpoint, the readout degree is three at index zero and 2k+2 at index k greater than zero.

**Theorem 1.3 (Sparse finite injectivity at equal total length).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.sparse_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.sparse_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let two positive paths each have n edges and equal total lengths. If the Gramian coefficients at the readout degrees for the first n-1 edges agree, their ordered lengths coincide. The two heat responses may have independent constant offsets. The readout set is empty for n at most one.

A difference at the first edge changes the cubic coefficient because a maps strictly decreasingly to 4/(3a^6). A first difference at a positive edge index changes the coefficient at that index's readout degree by the Jacobi prefix theorem. The equal sum determines the final edge once the preceding edges agree.

**Definition 1.4 (Least degree of the full jet).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.jetCutoff`

*Formalization.* `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.jetCutoff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cutoff is zero for at most one edge. For two or more edges it is the readout degree of the penultimate edge, which is three for two edges and 2n-2 for n at least three.

**Theorem 1.5 (The full jet identifies the path exactly at and above the cutoff).**

Lean statement: `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.finite_jet_injective_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.finite_jet_injective_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the number of edges and a positive total length. Agreement through degree d determines the ordered path for any independent constant heat offsets if and only if d is at least the cutoff.

The jet through the cutoff contains every sparse readout. For sharpness with n at least two, give the first n-1 edges length L/(n+1) and the last edge twice that length. Swapping the last two edges preserves positivity and the total L. The first differing edge is the penultimate one, and the Gramian coefficients agree at every degree below its readout degree.

## References

- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.cubic_coefficient`
- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.finite_jet_injective_iff`
- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.jetCutoff`
- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.readoutDegree`
- Truth anchor: `D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.sparse_injective`
- Dependency: [D5/S3/Quantum/Jacobi/NeumannHeatGramianJet](NeumannHeatGramianJet.md)
