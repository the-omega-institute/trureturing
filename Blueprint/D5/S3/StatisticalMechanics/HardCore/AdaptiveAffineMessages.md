# Adaptive affine message contraction

## Abstract

Whole-box positive affine messages on actual adaptive geometric types, up to activity 2.55.

**Definition 1.1 (Actual geometric child coefficients).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.childCoefficients`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.childCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The child is obtained from the actual adaptive radius-four transition. Missing directions have zero coefficients. All finite checks are performed on 881 actual rows.

**Definition 1.2 (Reconstruct the exact rational witness).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.rowWitness`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.rowWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pattern chooses lower, upper and interior coordinates. The level is reconstructed by the exact balance equation. The finite checker verifies positivity, all division results, clamping and the final margin; numerical stationary-point output is not a premise.

**Theorem 1.3 (All rational geometric rows).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_message_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_message_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every slope is nonnegative; every intercept minus slope is at least 10577 divided by one million. Each row passes CheckedRow with activity cap 51/20, probability floor 20/71, contraction constant 999/1000 and polynomial margin 3/1000. The script requests kernel reduction of these finite data.

**Definition 1.4 (Positive affine message).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affineMessage`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affineMessage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The message is intercept minus slope times the actual real vacancy probability.

**Definition 1.5 (Child message).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.childMessage`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.childMessage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the actual successor's affine message, with a zero contribution for an absent geometric direction.

**Definition 1.6 (Hard-core vacancy recursion).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.vacancy`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.vacancy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vacancy is one divided by one plus activity times the product of the three child vacancies. Missing children are represented by vacancy one.

**Theorem 1.7 (Uniform positivity).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_message_positive`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_message_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common positive lower bound holds at every real argument at most one, by nonnegativity of the slope and the exact endpoint certificate.

**Theorem 1.8 (Every probability tuple and every activity).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_polynomial_margin`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_polynomial_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic clamped-certificate theorem proves the margin throughout the full real box and the entire activity interval. No sampled-point assumption remains.

**Theorem 1.9 (Invariant real vacancy interval).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.vacancy_mem`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.vacancy_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual recursion maps the probability box back into the interval from 20/71 through one, uniformly for activities from zero through 51/20.

**Theorem 1.10 (Strict full-row contraction).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_full_row_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_full_row_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An exact denominator identity converts the polynomial margin to the weighted message-row inequality strictly below 999/1000. Identification of this expression with the logarithmic-coordinate Jacobian is derived separately in the theory appendix.

**Theorem 1.11 (Every child-pruning pattern).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_pruned_row_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_pruned_row_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Omitted child coordinates are set to one. Their nonnegative message contributions are removed from the full row, preserving strict contraction. The theorem quantifies over every subset, including the leaf case.

The exact rational and geometric verifier was executed. Lean elaboration and Scribe emission were not available. The holomorphic-coordinate extension, invariant complex neighborhoods and graph partition-polynomial induction are paper arguments in the existing theory volume, not conclusions of these Lean declarations.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affineMessage`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_full_row_contraction`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_message_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_message_positive`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_polynomial_margin`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.affine_pruned_row_contraction`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.childCoefficients`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.childMessage`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.rowWitness`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.vacancy`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages.vacancy_mem`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessageData](AdaptiveAffineMessageData.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates](AdaptiveRadiusFourCertificates.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate](AffineProductCertificate.md)
