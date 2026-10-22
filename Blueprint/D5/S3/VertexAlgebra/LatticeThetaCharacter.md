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

**Theorem 1.7 (Eta value of the actual trace character).**

Lean statement: `D5/S3/VertexAlgebra/LatticeThetaCharacter.actual_theta_character_eta`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeThetaCharacter.actual_theta_character_eta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordinary vacuum shift is minus rank/24. Absolute convergence and the grouped occupation HasSum identify the normalized literal neutral Sugawara traces with (eta(tau)/eta(2 tau))^rank on the upper half-plane.

**Theorem 1.8 (Modular S and identity-ground interchange).**

Lean statement: `D5/S3/VertexAlgebra/LatticeThetaCharacter.actual_theta_character_S`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeThetaCharacter.actual_theta_character_S` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual reflecting character at -1/tau equals 2^(rank/2) times (eta(tau)/eta(tau/2))^rank. The principal-root identity follows from the logarithm branch on the upper half-plane and positive real scaling. If the integral Gram determinant is a unit, symplectic coordinates make the rank even and the actual ground dimension is 2^(rank/2). The accepted half-Fock character with identity ground insertion and this actual ordinary trace character interchange under S. The half-Fock ground shift rank/16 and central charge rank give its vacuum exponent rank/48.

**Theorem 1.9 (Full positive-definite Sugawara eigenspace).**

Lean statement: `D5/S3/VertexAlgebra/LatticeThetaCharacter.positive_full_grade_eq_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeThetaCharacter.positive_full_grade_eq_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive real Gram form bounds the charge ellipsoid. Every label in the full signed-energy Sugawara kernel lies in the finite charge ellipsoid and finite oscillator sublevel. Its literal kernel equals the finite charge cutoff, with both original inverse Gram equations retained.

**Theorem 1.10 (Literal full-grade trace and character).**

Lean statement: `D5/S3/VertexAlgebra/LatticeThetaCharacter.positive_full_theta_character`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeThetaCharacter.positive_full_theta_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Theta is restricted from the original carrier to the full Sugawara kernel. Positive definiteness supplies finiteness before its trace is taken. The full trace at a negative energy is zero and at nonnegative energy is the signed integer coefficient. Its series is absolutely summable for norm q less than one, including q zero. The normalized full trace series has the same eta value and modular S law as the neutral actual character.

**Theorem 1.11 (Cofinal symmetric-charge regularization).**

Lean statement: `D5/S3/VertexAlgebra/LatticeThetaCharacter.symmetric_charge_cutoff_limit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeThetaCharacter.symmetric_charge_cutoff_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Symmetrizing arbitrary finite charge sets gives a directed cofinal exhaustion. For every signed energy, the actual finite cutoff traces stabilize exactly when zero is included. The normalized cutoff characters likewise stabilize to the actual neutral trace character. This is an explicit regularized limit for indefinite Gram forms; it is never a trace on an infinite full grade.

The insertion in the S interchange is the identity on the actual ground module. Arbitrary ground insertions, parity-S and full modular-group laws, module identities, fusion and sewing require further proofs. The reflecting trace is distinct from the ordinary uninserted full-charge Gaussian theta series.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.actual_theta_character_S`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.actual_theta_character_eta`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.actual_theta_trace_series`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoffActualGrade_finiteDimensional`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoffCoeffEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoffIndex_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.cutoff_theta_trace_neutral_sum`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.positive_full_grade_eq_cutoff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.positive_full_theta_character`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.symmetric_charge_cutoff_limit`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeThetaCharacter.thetaRestriction`
- Dependency: [D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation](../Combinatorics/Partitions/AnalyticIntegerOccupation.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](LatticeActualLZeroGrading.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeChargeCoercivity](LatticeChargeCoercivity.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCharacter](LatticeHalfFockCharacter.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeInvolution](LatticeInvolution.md)
