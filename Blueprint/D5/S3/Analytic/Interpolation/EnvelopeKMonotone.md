# The general moment envelope and its monotonicity

## Abstract

The logarithmic moment envelope increases with the mean and decreases with total squared deviation, giving a bound from an upper mean budget and a variance floor.

All coordinates and moment parameters are real, and k is a natural number. The variance parameter is the total squared deviation, without division by k. Use the following logarithmic function and radius parametrization.

$\operatorname{f}\left(t\right) = \log(1-\exp(-t))$

$\operatorname{g}\left(k, m, r\right) = \operatorname{f}\left(m+(k-1)r\right)+(k-1)\operatorname{f}\left(m-r\right)$

**Definition 1.1 (The envelope).**

$$\forall k: \operatorname{Nat}\left(\right), \forall m,V,r: \operatorname{Real}\left(\right), r = \sqrt{\frac{V}{k(k-1)}} \implies \operatorname{psiK}\left(k, m, V\right) = \operatorname{f}\left(m+(k-1)r\right)+(k-1)\operatorname{f}\left(m-r\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/EnvelopeKMonotone.psiK` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Define r as the square root of V divided by k(k-1), L as m-r, and H as m+(k-1)r. The value is f(H)+(k-1)f(L). Its positive domain is k at least two, m positive, and zero at most V strictly below k(k-1)m squared. On this domain both nodes are positive. The real logarithm and square root give a total real definition outside this domain as well.

**Theorem 1.2 (Strict increase in the mean).**

$$\forall k: \operatorname{Nat}\left(\right), \forall m,n,V: \operatorname{Real}\left(\right), (2 \le k \land 0 < m \land m < n \land V < k(k-1)(m)^{2}) \implies \operatorname{psiK}\left(k, m, V\right) < \operatorname{psiK}\left(k, n, V\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/EnvelopeKMonotone.psiK_strictMono_mean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least two, assume m is positive, m is less than n, and V is below k(k-1)m squared. Increasing m to n moves both positive nodes strictly to the right. Since f is strictly increasing and k-1 is positive, the envelope strictly increases. This statement also holds for negative V under the total real square-root convention; no nonnegativity premise on V is needed for this comparison.

**Theorem 1.3 (The derivative in the radius).**

$$\forall k: \operatorname{Nat}\left(\right), \forall m,r: \operatorname{Real}\left(\right), (2 \le k \land 0 \le r \land r < m) \implies \operatorname{HasDerivAt}\left(\operatorname{g}\left(k, m\right), (k-1)(\operatorname{deriv}\left(f, m+(k-1)r\right)-\operatorname{deriv}\left(f, m-r\right)), r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/EnvelopeKMonotone.radius_envelope_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be at least two and let zero be at most r strictly less than m. The upper node has velocity k-1 and the lower node has velocity minus one. The chain rule therefore gives the derivative (k-1) times the difference of the derivatives of f at the upper and lower nodes. Differentiability is an ordinary two-sided statement, including at radius zero.

**Theorem 1.4 (Strict decrease in the radius).**

$$\forall k: \operatorname{Nat}\left(\right), \forall m: \operatorname{Real}\left(\right), (2 \le k) \implies \operatorname{StrictAntiOn}\left(\operatorname{g}\left(k, m\right), \operatorname{Ico}\left(0, m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/EnvelopeKMonotone.radius_envelope_strictAnti` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real m and k at least two, g(k,m,r) is strictly decreasing on the half-open interval from zero to m. The assertion is vacuous if m is nonpositive. At an interior radius, the upper node exceeds the lower by kr. The second derivative of f is strictly negative on the positive half-line, so its first derivative strictly decreases. The displayed radius derivative is therefore strictly negative in the interior. Continuity at zero and the mean value theorem give strict decrease on the entire half-open interval.

**Theorem 1.5 (Strict decrease in total squared deviation).**

$$\forall k: \operatorname{Nat}\left(\right), \forall m,V,W: \operatorname{Real}\left(\right), (2 \le k \land 0 < m \land 0 \le V \land V < W \land W < k(k-1)(m)^{2}) \implies \operatorname{psiK}\left(k, m, W\right) < \operatorname{psiK}\left(k, m, V\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/EnvelopeKMonotone.psiK_strictAnti_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be at least two, m positive, and zero at most V strictly less than W strictly below k(k-1)m squared. The square root of V divided by k(k-1) is strictly smaller than the corresponding radius for W, and both radii lie between zero and m. Strict decrease in the radius gives the stated strict inequality. In particular, V may equal zero.

**Theorem 1.6 (The domain for positive coordinates).**

$$\forall k: \operatorname{Nat}\left(\right), \forall x: \operatorname{Fin}\left(k\right) \to \operatorname{Real}\left(\right), (2 \le k \land (\forall i: \operatorname{Fin}\left(k\right), 0 < \operatorname{x}\left(i\right))) \implies 0 \le \sum_{i \in \operatorname{Fin}\left(k\right)} (\operatorname{x}\left(i\right)-\frac{\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{x}\left(i\right)}{k})^{2} \land \sum_{i \in \operatorname{Fin}\left(k\right)} (\operatorname{x}\left(i\right)-\frac{\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{x}\left(i\right)}{k})^{2} < k(k-1)(\frac{\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{x}\left(i\right)}{k})^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/EnvelopeKMonotone.coordinate_variance_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let x be a positive real vector indexed by Fin k, with k at least two, and let m be its arithmetic mean. Its total squared deviation is nonnegative and strictly below k(k-1)m squared. The positive lower Hermite node gives a radius smaller than m; squaring and multiplying by the positive denominator gives the strict domain bound.

**Theorem 1.7 (A bound from two moment budgets).**

$$\forall k: \operatorname{Nat}\left(\right), \forall x: \operatorname{Fin}\left(k\right) \to \operatorname{Real}\left(\right), \forall M,v: \operatorname{Real}\left(\right), (2 \le k \land (\forall i: \operatorname{Fin}\left(k\right), 0 < \operatorname{x}\left(i\right)) \land 0 < M \land \frac{\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{x}\left(i\right)}{k} \le M \land v \le \sum_{i \in \operatorname{Fin}\left(k\right)} (\operatorname{x}\left(i\right)-\frac{\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{x}\left(i\right)}{k})^{2} \land v < k(k-1)(M)^{2}) \implies \sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{f}\left(\operatorname{x}\left(i\right)\right) \le \operatorname{psiK}\left(k, M, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/EnvelopeKMonotone.sum_logValue_le_psiK` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let x be a positive real vector on Fin k, with k at least two. Let its arithmetic mean be at most the positive upper budget M. Suppose v is at most the actual total squared deviation and is strictly below k(k-1)M squared. Then the logarithmic coordinate sum is at most psiK(k,M,v). Apply the Hermite bound at the actual moments, increase the mean to M, and decrease the radius to the one specified by v. No positive lower mean budget is needed. For v negative, the total real square root is zero, and the same weak radius comparison remains valid; the strict variance theorem retains its nonnegative domain.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/EnvelopeKMonotone.coordinate_variance_domain`
- Truth anchor: `D5/S3/Analytic/Interpolation/EnvelopeKMonotone.psiK`
- Truth anchor: `D5/S3/Analytic/Interpolation/EnvelopeKMonotone.psiK_strictAnti_variance`
- Truth anchor: `D5/S3/Analytic/Interpolation/EnvelopeKMonotone.psiK_strictMono_mean`
- Truth anchor: `D5/S3/Analytic/Interpolation/EnvelopeKMonotone.radius_envelope_hasDerivAt`
- Truth anchor: `D5/S3/Analytic/Interpolation/EnvelopeKMonotone.radius_envelope_strictAnti`
- Truth anchor: `D5/S3/Analytic/Interpolation/EnvelopeKMonotone.sum_logValue_le_psiK`
- Dependency: [D5/S3/Analytic/Interpolation/HermiteMomentBounds](HermiteMomentBounds.md)
- Dependency: [D5/S3/Analytic/Interpolation/HermiteUpperEnvelope](HermiteUpperEnvelope.md)
- Dependency: [D5/S3/Analytic/Interpolation/LogOneSubExpDerivatives](LogOneSubExpDerivatives.md)
- Dependency: [D5/S3/Analytic/Interpolation/TwoPointGridDominance](TwoPointGridDominance.md)
