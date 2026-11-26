# Similarity of trace-zero binary matrices of size three

## Abstract

Every nonzero trace-zero binary matrix of size three is similar to one of six explicit matrices.

**Definition 1.1 (The six representatives).**

Lean statement: `D5/S1/Eigenstructure/BinaryTraceZeroSimilarity.representative`

*Formalization.* `D5/S1/Eigenstructure/BinaryTraceZeroSimilarity.representative` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *A structural dissociation gain in every connected Heawood double cover*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L68-L108>.

*Commentary.*

Write Eij for a matrix unit with one-based indices. The representatives in order are E12, E12+E23, diag(1,1,0), diag(1,1,0)+E12, E13+E21+E32, and E13+E21+E32+E23.

**Theorem 1.2 (Conjugacy to a chosen representative).**

Lean statement: `D5/S1/Eigenstructure/BinaryTraceZeroSimilarity.exists_conjugate`

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/BinaryTraceZeroSimilarity.exists_conjugate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *A structural dissociation gain in every connected Heawood double cover*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L68-L108>.

*Commentary.*

A nonzero binary matrix of size three and trace zero has characteristic polynomial X cubed plus a times X plus c. The two coefficients are binary. For c equal to zero, the nilpotent or repeated-root theorem supplies an ordered normal basis. For c equal to one, a cyclic basis gives the companion matrix.

The change-of-basis matrix is invertible and conjugates the chosen representative to the input matrix.

The matrices match the switching invariants of the six signings in the Heawood double cover classification.

## References

- Truth anchor: `D5/S1/Eigenstructure/BinaryTraceZeroSimilarity.exists_conjugate`
- Truth anchor: `D5/S1/Eigenstructure/BinaryTraceZeroSimilarity.representative`
- Dependency: [D5/S1/Eigenstructure/BinaryCubicCompanion](BinaryCubicCompanion.md)
- Dependency: [D5/S1/Eigenstructure/BinaryCubicRepeatedRoot](BinaryCubicRepeatedRoot.md)
- Dependency: [D5/S1/Eigenstructure/NilpotentDimensionThree](NilpotentDimensionThree.md)
- Dependency: [D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity](../Recurrence/Residue/ExponentialSquareWeightCatalanParity.md)
