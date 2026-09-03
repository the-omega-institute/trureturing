# Cauchy-Feature Right Inverse

## Abstract

Distinct supports away from one center give a nonsingular reciprocal Cauchy-jet feature matrix.

**Definition 1.1 (Reciprocal affine Cauchy node).**

Lean statement: `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.reciprocalCauchyNode`

*Formalization.* `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.reciprocalCauchyNode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each support coordinate is translated by one center and inverted.

**Definition 1.2 (Cauchy-jet feature matrix).**

Lean statement: `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchyJetFeatureMatrix`

*Formalization.* `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchyJetFeatureMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix is a nonzero reciprocal diagonal factor times the existing Vandermonde matrix.

**Definition 1.3 (Canonical Cauchy-jet inverse).**

Lean statement: `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchyJetFeatureRightInverse`

*Formalization.* `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchyJetFeatureRightInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical certificate is Mathlib's nonsingular matrix inverse.

**Theorem 1.4 (Distinct supports give a nonzero determinant).**

Lean statement: `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchy_jet_feature_det_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchy_jet_feature_det_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Injectivity survives common translation and inversion. The determinant factors into a nonzero diagonal product and a nonzero Vandermonde determinant.

**Theorem 1.5 (The Cauchy-jet inverse is two-sided).**

Lean statement: `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchy_feature_right_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchy_feature_right_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonsingular inverse supplies both matrix inverse identities and an injective finite analysis map.

## References

- Truth anchor: `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.reciprocalCauchyNode`
- Truth anchor: `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchyJetFeatureMatrix`
- Truth anchor: `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchyJetFeatureRightInverse`
- Truth anchor: `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchy_jet_feature_det_ne_zero`
- Truth anchor: `D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchy_feature_right_inverse`
