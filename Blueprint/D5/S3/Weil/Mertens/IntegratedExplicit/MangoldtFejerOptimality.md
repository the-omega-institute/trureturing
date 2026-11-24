# Cosine moments on a half interval

## Abstract

The optimal coefficient in the Fejér average

Let μ be a probability measure carried by the interval from zero to one half. Write A for the μ-average of b/2 − b² and C(t) for the μ-average of cos(tb).

**Theorem 1.1 (The exact Fourier correction).**

$$A = \frac{1}{24} - \frac{\sum_{n=1}^{\infty} \frac{\operatorname{C}\left(4 \cdot \pi \cdot n\right)}{n^{2}}}{4 \cdot \pi^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerOptimality.integral_gap_eq_sub_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluate Mathlib's cosine series for the second Bernoulli polynomial at 2b. The absolute values of its terms are bounded by the reciprocal squares, which permits termwise integration against any such μ, including measures with atoms.

**Theorem 1.2 (The bound and its equality condition).**

$$A \le \frac{1}{24} \land \left(A = \frac{1}{24} \Leftrightarrow \left(\forall n \in PositiveIntegers,\; \operatorname{C}\left(4 \cdot \pi \cdot n\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerOptimality.integral_gap_le_and_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If each cosine moment at frequency 4πn is nonnegative for positive integers n, the correction is a sum of nonnegative terms. It vanishes exactly when every such moment vanishes.

The differences of two independent uniform points on the half interval give the triangular law and attain 1/24. The arithmetic estimate in MangoldtUniformFejerGap uses half of the average, which gives the coefficient 1/48 for this averaging argument.

**Theorem 1.3 (The attained arithmetic coefficient).**

$$maximumCoefficient = \frac{1}{48}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerOptimality.isGreatest_fejer_averaging_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here maximumCoefficient is the greatest value of A/2 among the probability measures with C(t) nonnegative for every real t. The density 4 − 8b gives C(0) = 1. For nonzero t, integration gives C(t) = 8(1 − cos(t/2))/t² and zero at every positive harmonic. The equality condition yields attainment.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerOptimality.integral_gap_eq_sub_tsum`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerOptimality.integral_gap_le_and_eq_iff`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerOptimality.isGreatest_fejer_averaging_coefficient`
