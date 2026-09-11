# LiCurvatureLevyDecomposition

## Abstract

Circle probability measures, the existing negative-power Fourier moments, and the existing Toeplitz matrices.

**Theorem 1.1 (The identity contributes a quadratic term).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.geometric_energy_at_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.geometric_energy_at_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original finite geometric polynomial has energy n squared at the circle identity.

**Theorem 1.2 (The same energy is the compensated jump kernel).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.geometric_energy_off_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.geometric_energy_off_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Away from the identity, derive the exact quotient from the finite geometric-sum identity and unit modulus. The denominator is proved nonzero.

**Theorem 1.3 (Keep the cancellation inside the integral).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.li_jump_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.li_jump_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compensated jump expression is integrable for every finite source measure. Finite total mass of the singular jump weight is not assumed.

**Theorem 1.4 (Separate the identity atom and the jump contribution).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.reconstructed_li_levy_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.reconstructed_li_levy_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact original energy contains its identity mass times n squared and the compensated positive jump expression. No probability-process existence theorem is asserted.

**Theorem 1.5 (Identity mass forces quadratic growth).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.identity_atom_energy_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.identity_atom_energy_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative scale, the remaining jump contribution is nonnegative and the identity atom gives a quadratic lower bound.

**Theorem 1.6 (Subquadratic growth excludes the Cayley boundary atom).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.identity_atom_vanishes_of_subquadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.identity_atom_vanishes_of_subquadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive scale and a subquadratic limit force zero mass at the actual circle identity, which is absent from every finite real Cayley image.

**Theorem 1.7 (Construct the pure jump representation from curvature data).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.normalized_curvature_jump_representation`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.normalized_curvature_jump_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All normalized curvature matrices, the original recurrence, positive first coefficient and subquadratic growth construct the same moment measure, exclude its identity atom, and represent each original coefficient by the compensated jump integral.

## References

- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.geometric_energy_at_identity`
- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.geometric_energy_off_identity`
- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.identity_atom_energy_floor`
- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.identity_atom_vanishes_of_subquadratic`
- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.li_jump_integrable`
- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.normalized_curvature_jump_representation`
- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureLevyDecomposition.reconstructed_li_levy_decomposition`
- Dependency: [D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion](LiCurvatureProbabilityCompletion.md)
