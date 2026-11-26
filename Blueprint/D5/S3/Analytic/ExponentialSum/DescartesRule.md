# Descartes rule for exponential sums

## Abstract

The generalized Descartes rule for real exponential sums, including strict sign reversals at a saturated set of zeros.

Let N be any natural number, let a and mu be real families indexed by Fin N, and assume that mu is strictly decreasing. Write F(t) for the sum of a(i) exp(mu(i)t), and V for List.signVariations of List.ofFn a. This variation count removes all zero coefficients before counting adjacent opposite signs. All exponents and arguments are real.

**Theorem 1.1 (Distinct zeros).**

Lean statement: `D5/S3/Analytic/ExponentialSum/DescartesRule.zero_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExponentialSum/DescartesRule.zero_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If at least one coefficient is nonzero, every finite set Z consisting of zeros of F has cardinality at most V. The bound holds for arbitrary real exponents; no integral or rational spacing assumption is imposed.

After removing zero terms, choose a constant c strictly between the exponents at a coefficient sign reversal. Multiplication by exp(-ct) preserves zeros. Its derivative has coefficients a(i)(mu(i)-c), whose variation count is exactly V-1. Induction on V and Rolle's theorem give the bound. When V is zero, all terms have the same strict sign.

**Theorem 1.2 (A prescribed stationary zero).**

Lean statement: `D5/S3/Analytic/ExponentialSum/DescartesRule.zero_bound_with_stationary_root`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExponentialSum/DescartesRule.zero_bound_with_stationary_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume some coefficient is nonzero and every point of the finite set Z is a zero of F. If the derivative of F also vanishes at a point z of Z, then the cardinality of Z plus one is at most V.

Multiplication by the normalizing exponential preserves stationarity at z because F(z) is zero. The normalized derivative vanishes at z and, by Rolle's theorem, at an interior point between each pair of consecutive points of Z. For example, coefficients (1, −2, 1) and exponents (0, −1, −2) give F(t) = (1 − exp(−t))². With Z = {0}, the bound is attained with two sign variations.

**Theorem 1.3 (Zeros without a sign reversal).**

Lean statement: `D5/S3/Analytic/ExponentialSum/DescartesRule.sign_crossing_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExponentialSum/DescartesRule.sign_crossing_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same assumptions, add to the cardinality of Z the number of its points where F fails ChangesSign. The result is still at most V. Here ChangesSign F z means that some epsilon greater than zero makes F(t)F(s) strictly negative for every t between z-epsilon and z and every s between z and z+epsilon.

The proof first establishes the stronger bound that charges each stationary zero one additional unit. The normalized derivative has a zero between consecutive prescribed zeros and at every prescribed stationary zero. These sets are disjoint. A nonzero derivative at a zero forces a uniform strict sign reversal, giving the stated conclusion.

**Theorem 1.4 (Exact signs at saturation).**

Lean statement: `D5/S3/Analytic/ExponentialSum/DescartesRule.exact_sign`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExponentialSum/DescartesRule.exact_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose some coefficient a(i) is strictly positive and all coefficients at earlier indices vanish. If Z is a finite set of zeros with cardinality exactly V, then at every real t the SignType sign of F(t) equals that of the product over z in Z of t-z. The conclusion includes the value zero at the prescribed points and the empty product when V is zero.

Saturation excludes every additional zero and every stationary prescribed zero. Normalization by the largest exponent with a nonzero coefficient tends to its positive coefficient, so F is eventually positive. Removing each simple zero with the continuous divided slope leaves a continuous function with exactly the remaining simple zeros. Induction gives the monic product's sign. This is a form of the classical generalized Descartes principle; the proof supplies an interface for real exponential sums.

## References

- Truth anchor: `D5/S3/Analytic/ExponentialSum/DescartesRule.exact_sign`
- Truth anchor: `D5/S3/Analytic/ExponentialSum/DescartesRule.sign_crossing_bound`
- Truth anchor: `D5/S3/Analytic/ExponentialSum/DescartesRule.zero_bound`
- Truth anchor: `D5/S3/Analytic/ExponentialSum/DescartesRule.zero_bound_with_stationary_root`
