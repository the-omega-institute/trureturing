# Finite Hermitian Inertia Stability

## Abstract

Two-sided Weyl certificates preserve finite Hermitian inertia across an invertible perturbation.

**Definition 1.1 (Eigenvalue radius bound).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.HasEigenvalueRadiusBound`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.HasEigenvalueRadiusBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every eigenvalue of a Hermitian perturbation lies in a prescribed closed radius.

**Definition 1.2 (Two-sided perturbation radius).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.HasTwoSidedEigenvalueRadiusBound`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.HasTwoSidedEigenvalueRadiusBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The perturbation and its negative receive separate radius certificates, independent of eigenvalue enumeration.

**Definition 1.3 (Positive threshold gap).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.HasPositiveThresholdGap`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.HasPositiveThresholdGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Raising the counting threshold from zero removes no positive eigenvalues.

**Definition 1.4 (Two-sided threshold gap).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.HasTwoSidedThresholdGap`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.HasTwoSidedThresholdGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix and its negative have no counted eigenvalue in the threshold strip next to zero.

**Theorem 1.5 (Positive-index lower stability).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.posIndex_le_add_of_threshold_gap`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.posIndex_le_add_of_threshold_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A threshold gap and a reverse perturbation bound prevent the positive index from decreasing.

**Theorem 1.6 (Negative-index lower stability).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.negIndex_le_add_of_threshold_gap`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.negIndex_le_add_of_threshold_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A threshold gap for the negated base and a perturbation bound prevent the negative index from decreasing.

**Theorem 1.7 (Two-sided inertia stability).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.inertia_eq_of_two_sided_weyl_certificate`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.inertia_eq_of_two_sided_weyl_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two-sided Weyl certificates and invertible endpoints force equality of both inertia counts.

**Theorem 1.8 (Hermitian-signature stability).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.hermitianSignature_add_eq_of_two_sided_weyl_certificate`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.hermitianSignature_add_eq_of_two_sided_weyl_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same certificate preserves the repository's existing Hermitian signature coordinate.

## References

- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.HasEigenvalueRadiusBound`
- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.HasTwoSidedEigenvalueRadiusBound`
- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.HasPositiveThresholdGap`
- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.HasTwoSidedThresholdGap`
- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.posIndex_le_add_of_threshold_gap`
- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.negIndex_le_add_of_threshold_gap`
- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.inertia_eq_of_two_sided_weyl_certificate`
- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianInertiaStability.hermitianSignature_add_eq_of_two_sided_weyl_certificate`
- Dependency: [D5/S3/Weil/ZetaLinear/Weyl](../Weil/ZetaLinear/Weyl.md)
- Dependency: [D5/S3/SpectralTopology/PointGapExactInertia](PointGapExactInertia.md)
- Dependency: [D5/S3/SpectralTopology/FiniteSpectralLocalizer](FiniteSpectralLocalizer.md)
