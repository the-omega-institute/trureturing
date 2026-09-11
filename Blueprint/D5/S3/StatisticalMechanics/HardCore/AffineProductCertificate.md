# Affine product certificates

## Abstract

Exact clamped product certificates for full-box hard-core affine messages.

**Theorem 1.1 (A global product bound from a clamped witness).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.clipped_product_bound`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.clipped_product_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Divide the affine residual by the positive level and the three coordinates by their reference values. The clamping inequalities make the sum of these four nonnegative factors at most four. Mathlib's AM-GM theorem bounds their product by one. The negative-residual case is handled separately. A local numerical optimum is never assumed global.

**Definition 1.2 (Rational proposal data).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.ClipWitness`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.ClipWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A witness stores a rational level and three rational reference coordinates. Validity is a separate proposition.

**Definition 1.3 (Exact finite certificate obligations).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.CheckedRow`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.CheckedRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A present witness must satisfy positivity, interval bounds, exact balance, the three clamping alternatives and the rational margin. The absent-witness case proves that the residual has the favorable sign throughout the box.

**Theorem 1.4 (Every real point and every smaller activity).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.checked_row_sound`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.checked_row_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The checked rational data imply the polynomial margin on the entire real box and throughout the nonnegative activity interval. This theorem supplies the continuous semantic bridge consumed by the concrete adaptive-grid certificate.

The general AM-GM principle is prior art and reused from Mathlib. These proof scripts have not been elaborated in the authoring runtime.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.CheckedRow`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.ClipWitness`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.checked_row_sound`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.clipped_product_bound`
