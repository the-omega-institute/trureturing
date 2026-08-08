# Midslope Curvature Values

## Abstract

The remaining rationalizable midslope-curvature integrals have exact values.

**Theorem 1.1 (The negative-half value is half the geometric value).**

$$J(-\frac{1}{2})=\frac{J(0)}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/MidslopeCurvatureValues.J_neg_half_eq_half_J_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the open unit interval, twice the negative-half mean is two times 1 - t squared divided by one plus its square root. The resulting bracket is exactly half the geometric-mean bracket, so interval-integral linearity proves the relation without first evaluating either integral.

**Theorem 1.2 (The geometric value is one minus two log two).**

$$J(0)=1-2 \log 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/MidslopeCurvatureValues.J_zero_eq_one_sub_two_log_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The producer integrand first reduces to minus one divided by the product of 1 + t and 1 + sqrt(1 - t squared). The substitution t = 2u / (1 + u squared) rationalizes it to 1 - 2 / (1 + u) on the unit interval. Mathlib's reciprocal integral then supplies the logarithm.

**Theorem 1.3 (The half-power value is five sixths minus two log two).**

$$J(\frac{1}{2})=\frac{5-12 \log 2}{6}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/MidslopeCurvatureValues.J_half_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Twice the half-power mean is one half of 1 + sqrt(1 - t squared). The same rationalizing substitution turns the producer integrand into -u squared / 2 + u + 1 / 2 - 2 / (1 + u), whose polynomial and reciprocal parts integrate exactly.

**Theorem 1.4 (The half-power value is an affine combination).**

$$J(\frac{1}{2})=\frac{5}{6}J(0)+\frac{1}{3}J(1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/MidslopeCurvatureValues.J_half_eq_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting the exact half-power and geometric values together with the frozen arithmetic value reduces the relation to a ring identity in 1 and log 2.

## References

- Truth anchor: `D5/S3/Constants/MidslopeCurvatureValues.J_zero_eq_one_sub_two_log_two`
- Truth anchor: `D5/S3/Constants/MidslopeCurvatureValues.J_half_eq_affine`
- Truth anchor: `D5/S3/Constants/MidslopeCurvatureValues.J_half_eq`
- Truth anchor: `D5/S3/Constants/MidslopeCurvatureValues.J_neg_half_eq_half_J_zero`
- Dependency: [D5/S3/Constants/MidslopeCurvature](MidslopeCurvature.md)
