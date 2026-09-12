# LiCurvatureSchoenbergSemigroup

## Abstract

The constructed Li probability evolution closes the specific forward Schoenberg connection.

**Theorem 1.1 (Actual probability evolution from the original energy).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.reconstructed_li_probability_semigroup`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.reconstructed_li_probability_semigroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integrated geometric Gram and forward Schoenberg prove every exponential matrix condition needed by the existing circle semigroup constructor.

**Theorem 1.2 (Natural multiples are iterated convolution).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.semigroup_nsmul_convolution`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.semigroup_nsmul_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural multiple of a time is the actual repeated multiplicative convolution beginning with delta at the identity.

**Theorem 1.3 (Probability roots of every positive order).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.semigroup_probability_roots`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.semigroup_probability_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The root is the same probability family at time t divided by the positive integer order; the iterated convolution is proved equal to the original marginal.

**Theorem 1.4 (Negative type from the original curvature data).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.normalized_curvature_conditionally_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.normalized_curvature_conditionally_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The representing measure is constructed from the normalized positive curvature and original recurrence. All finite integer samples and zero-sum real vectors are covered.

**Theorem 1.5 (Control the entire original coefficient growth).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.normalized_curvature_quadratic_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.normalized_curvature_quadratic_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed probability representation gives zero-to-L1-times-n-squared bounds at every index. This supplies a concrete bound for a subsequent canonical generating-function continuation.

**Theorem 1.6 (Full normalized-curvature probability evolution).**

Lean statement: `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.normalized_curvature_probability_evolution`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.normalized_curvature_probability_evolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same original Li-type sequence determines a unique weakly continuous probability semigroup and all convolution roots. No representing measure, negative-type property or exponential positivity is supplied as an additional premise.

## References

- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.normalized_curvature_conditionally_negative`
- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.normalized_curvature_probability_evolution`
- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.normalized_curvature_quadratic_bound`
- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.reconstructed_li_probability_semigroup`
- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.semigroup_nsmul_convolution`
- Truth anchor: `D5/S3/Weil/Probability/LiCurvatureSchoenbergSemigroup.semigroup_probability_roots`
- Dependency: [D5/S3/Weil/Probability/GeometricLiNegativeType](GeometricLiNegativeType.md)
