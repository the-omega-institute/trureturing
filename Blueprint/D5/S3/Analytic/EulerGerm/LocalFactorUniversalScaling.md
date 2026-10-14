# Golden Local-Factor Universal Scaling

## Abstract

Golden prime-local factors are logarithmic rescalings of one universal series, and their second normalized deviations are absolutely summable under the sharper sufficient bound one over twice phi cubed.

**Theorem 1.1 (Prime-local factors are logarithmic rescalings).**

$$\forall p \in \operatorname{Primes}\left(\mathbb{N}\right), q \in \operatorname{Primes}\left(\mathbb{N}\right), s \in \mathbb{C},\; \operatorname{germLocalFactor}\left(s, p\right) = \operatorname{germLocalFactor}\left(\frac{\operatorname{log}\left(p\right)}{\operatorname{log}\left(q\right)} \times s, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling.germLocalFactor_prime_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive prime bases, the principal complex power is the exponential of the exponent times the real logarithm. After multiplying the argument by log p over log q, every term of the q-local series equals the matching p-local term.

The identity asserts only universal scaling. It does not assert that any local factor has a zero.

**Theorem 1.2 (The normalized local factor exposes its next mode and exact tail).**

$$\forall s \in \mathbb{C}, p \in \operatorname{Primes}\left(\mathbb{N}\right),\; 0 < \Re(s) \Rightarrow (1 - p^{-s \times \varphi^{3}}) \times (1 + p^{-s \times \varphi^{2}})^{-1} \times \operatorname{germLocalFactor}\left(s, p\right) - 1 = -(p^{-s \times \varphi^{3}})^{2} + (1 - p^{-s \times \varphi^{3}}) \times (1 + p^{-s \times \varphi^{2}})^{-1} \times \sum_{k\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}\left(k + 4\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling.germLocalFactor_next_mode_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first four exponent values are zero, phi squared, phi cubed, and phi to the fourth. Since phi to the fourth is phi squared plus phi cubed, those four terms factor as one plus x times one plus y.

For positive real part, the norm of x is strictly below one, so the displayed inverse is legitimate. The remaining sum starts exactly at o5Beta of four.

**Theorem 1.3 (The second normalized deviations have a sharper sufficient bound).**

$$\forall s \in \mathbb{C},\; \frac{1}{2 \times \varphi^{3}} < \Re(s) \Rightarrow \operatorname{Summable}\left(p: \operatorname{Primes}\left(\mathbb{N}\right) \mapsto \left\lVert (1 - p^{-s \times \varphi^{3}}) \times (1 + p^{-s \times \varphi^{2}})^{-1} \times \operatorname{germLocalFactor}\left(s, p\right) - 1 \right\rVert\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling.second_normalized_factor_deviation_norm_summable_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The leading deviation is the square of the phi-cubed mode. Its prime sum is summable under the sufficient strict inequality two times phi cubed times the real part of s greater than one; the tail is controlled from o5Beta of four onward.

This gives a sharper sufficient bound, improving one over phi to the fourth to one over twice phi cubed. It asserts no zero of any local factor.

**Theorem 1.4 (The prime-three orbit straddles the window while prime five exits below it).**

$$
\frac{1}{2\varphi^3}<\operatorname{goldenCandidateOrbit}(3)<\frac{1}{\varphi^2}
\quad\text{and}\quad
\operatorname{goldenCandidateOrbit}(5)<\frac{1}{2\varphi^3}
$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling.gc_orbit_two_prime_straddle` (`✓ std3`). ∎

*Commentary.*

The prime-two candidate is transported through the universal prime scaling by the factor `log 2 / log p`. The proof uses strict logarithm monotonicity, rational bounds for the golden ratio, and `2^9 < 5^4`. It locates the scaled candidate; it does not assert that the transported point is a local-factor zero.

**Theorem 1.5 (Prime channels in the scaled golden window).**

$$
\forall p\in\operatorname{Primes}(\mathbb N),\quad
\left(\frac{1}{2\varphi^3}<\operatorname{goldenCandidateOrbit}(p)<\frac{1}{\varphi^2}\right)
\iff p=2\ \lor\ p=3.
$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling.scaled_gc_orbit_window_iff` (`✓ std3`). ∎

*Commentary.*

For `p ≥ 5`, logarithm monotonicity reduces the upper estimate to the `p = 5` comparison. The theorem is a discrete orbit-window classification and supplies no Riemann-hypothesis conclusion by itself.

## References

- Truth anchor: `D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling.germLocalFactor_next_mode_expansion`
- Truth anchor: `D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling.germLocalFactor_prime_scaling`
- Truth anchor: `D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling.second_normalized_factor_deviation_norm_summable_sharp`
- Truth anchor: `D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling.gc_orbit_two_prime_straddle`
- Truth anchor: `D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling.scaled_gc_orbit_window_iff`
