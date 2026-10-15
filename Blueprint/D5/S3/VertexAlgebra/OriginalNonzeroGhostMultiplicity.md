# Actual Nonzero-Charge Transverse Multiplicity

## Abstract

At each integral native level, the released original projection has an explicit finite weighted-transverse basis with native J degrees one and two.

**Theorem 1.1 (Finite actual transverse index).**

$$level \Rightarrow \operatorname{Finite}\left(transverseLevelIndex\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalNonzeroGhostMultiplicity.transverseLevelIndex_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index contains all finite oscillator exponents with both longitudinal occupations zero, ghost subset contained in {3}, and exact native level.

**Theorem 1.2 (Complete basis and exact count).**

$$\operatorname{finrank}\left(Complex, nativeTransverseEnergySpace\right) = \operatorname{card}\left(transverseLevelIndex\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalNonzeroGhostMultiplicity.nativeTransverseEnergy_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The range-energy space is spanned by the actual native words and the index map is linearly independent; this is not a formal generating function.

**Theorem 1.3 (Native J degrees).**

$$J = degree\times basis$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalNonzeroGhostMultiplicity.nativeTransverseEnergyBasis_J_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty ghost partner has native degree one and the c0 partner has native degree two. The absolute partner is retained.

**Theorem 1.4 (Actual transfer covariance).**

$$J \in finiteOriginalCorrectionInverse = 0, J \in finiteOriginalTransferredDifferential = finiteOriginalTransferredDifferential$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalNonzeroGhostTransferJ.J0_finite_transferred_differential_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual finite original-Q transfer has a genuine native J degree. The true quotient transfer remains the original Q transfer, not reduced delta cohomology.

## References

- Truth anchor: `D5/S3/VertexAlgebra/OriginalNonzeroGhostMultiplicity.nativeTransverseEnergyBasis_J_degree`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalNonzeroGhostMultiplicity.nativeTransverseEnergy_finrank`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalNonzeroGhostMultiplicity.transverseLevelIndex_finite`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalNonzeroGhostTransferJ.J0_finite_transferred_differential_commutator`
