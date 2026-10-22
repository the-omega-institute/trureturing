# Actual Lattice Theta Character

## Abstract

Actual finite-charge restrictions of the all-charge Sugawara zero mode.

**Definition 1.1 (Finite cutoff coefficient equivalence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoffCoeffEquiv`

*Formalization.* `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoffCoeffEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The charge-supported actual Sugawara eigenspace is identified with finitely supported coefficients on the literal charge and energy cutoff. The original H, H*gramComplex D = 1, and gramComplex D*H = 1 hypotheses are retained.

**Theorem 1.2 (Finite fixed-charge energy fibres).**

Lean statement: `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoffIndex_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoffIndex_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite charge set and every signed integer energy, the literal cutoff index is finite by oscillatorLeFinite and a dependent finite charge sum.

**Theorem 1.3 (Finite actual cutoff eigenspaces).**

Lean statement: `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoffActualGrade_finiteDimensional`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoffActualGrade_finiteDimensional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual charge-supported Sugawara eigenspace is finite-dimensional through its actual coefficient basis. This does not invoke a trace on an infinite full grade.

**Definition 1.4 (Actual reflected restriction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeThetaCharacter.thetaRestriction`

*Formalization.* `D5/S3/VertexAlgebra/LatticeThetaCharacter.thetaRestriction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a symmetric finite charge set, thetaLinear is restricted to the actual charge-supported Sugawara eigenspace. The restriction is built by codRestrict and domRestrict from the actual operator.

**Theorem 1.5 (Finite actual theta trace).**

Lean statement: `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoff_theta_trace_neutral_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoff_theta_trace_neutral_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite matrix trace of the actual restricted theta operator is the signed occupation sum over the neutral charge labels. Reflection is applied before diagonal cancellation, and no infinite-grade or scalar proxy trace is used.

**Theorem 1.6 (Actual trace series).**

Lean statement: `D5/S3/VertexAlgebra/LatticeThetaCharacter.actual_theta_trace_series`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeThetaCharacter.actual_theta_trace_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The neutral actual traces are grouped by integer oscillator energy. The signed occupation majorant gives absolute summability and a HasSum for the actual coefficient series, including the zero-rank case and complex phases.

The full positive-grade specialization, named indefinite cutoff limit, eta normalization, and identity-ground S endpoint remain open in this implementation checkpoint.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.actual_theta_trace_series`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoffActualGrade_finiteDimensional`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoffCoeffEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoffIndex_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoff_theta_trace_neutral_sum`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.thetaRestriction`
- Dependency: [D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation](../Combinatorics/Partitions/AnalyticIntegerOccupation.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](LatticeActualLZeroGrading.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeChargeCoercivity](LatticeChargeCoercivity.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCharacter](LatticeHalfFockCharacter.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeInvolution](LatticeInvolution.md)
