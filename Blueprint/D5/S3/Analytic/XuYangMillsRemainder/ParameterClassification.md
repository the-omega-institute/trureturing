# Parameter thresholds for the original Mills remainder

## Abstract

Both sign classifications for the Gaussian Mills remainder at every truncation order.

**Definition 1.1 (B).**

$$\forall j \in \mathbb {N},\; \operatorname {B}\left(j\right) = \operatorname {intervalIntegral}\left(v: \mathbb {R}\mapsto \left(v\right)^{2} \cdot \left(1 + \left(v\right)^{2}\right)^{j}, 0, 1, \operatorname {volume}\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/ParameterClassification.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second polynomial moment is integrated over the unit interval. The companion zeroth moment is Result.intPow. Both are finite, and the second moment is strictly between zero and the zeroth moment.

**Definition 1.2 (theta).**

$$\forall j \in \mathbb {N},\; \operatorname {theta}\left(j\right) = \frac{1 - \frac{\operatorname {Result.intPow}\left(j\right)}{\operatorname {B}\left(j\right)}}{2}$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/ParameterClassification.theta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The threshold uses the ratio of the zeroth polynomial moment to the second polynomial moment. Its denominator is strictly positive at every natural order.

**Theorem 1.3 (result).**

$$\forall n \in \mathbb {N},\; \left(2 \le n\right) \Rightarrow \left(\forall a \in \mathbb {R},\; \left(\left(\left(\forall x \in \mathbb {R},\; \left(0 < x\right) \Rightarrow \left(0 \le \left(-1\right)^{n} \cdot \operatorname {Result.D}\left(n, x, a\right)\right)\right) \Leftrightarrow \left(\operatorname {Result.CompletelyMonotoneOn}\left(x: \mathbb {R}\mapsto \left(-1\right)^{n} \cdot \operatorname {Result.D}\left(n, x, a\right)\right)\right)\right) \land \left(\left(\operatorname {Result.CompletelyMonotoneOn}\left(x: \mathbb {R}\mapsto \left(-1\right)^{n} \cdot \operatorname {Result.D}\left(n, x, a\right)\right)\right) \Leftrightarrow \left(a \le \operatorname {theta}\left(n - 2\right)\right)\right)\right) \land \left(\left(\left(\forall x \in \mathbb {R},\; \left(0 < x\right) \Rightarrow \left(0 \le -\left(\left(-1\right)^{n} \cdot \operatorname {Result.D}\left(n, x, a\right)\right)\right)\right) \Leftrightarrow \left(\operatorname {Result.CompletelyMonotoneOn}\left(x: \mathbb {R}\mapsto -\left(\left(-1\right)^{n} \cdot \operatorname {Result.D}\left(n, x, a\right)\right)\right)\right)\right) \land \left(\left(\operatorname {Result.CompletelyMonotoneOn}\left(x: \mathbb {R}\mapsto -\left(\left(-1\right)^{n} \cdot \operatorname {Result.D}\left(n, x, a\right)\right)\right)\right) \Leftrightarrow \left(\operatorname {theta}\left(n - 1\right) \le a\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/ParameterClassification.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every truncation order n at least two and every real a, global nonnegativity of the signed original remainder is equivalent to complete monotonicity and to the lower parameter range. The same equivalences for its negative give the upper parameter range. Both endpoints are included. Result.D uses the Gaussian tail Result.millsRatio, the original Gamma coefficients Result.u and the finite sum from one through n, with b equal to a minus two. Complete monotonicity includes smoothness and every derivative order, including zero. The weighted Taylor moments bound the signed Laplace density. Its polynomial envelope permits all Laplace derivatives. Clearing the finite remainder at zero proves the lower parameter restriction; the next remainder and its polynomial Laplace bound give the leading coefficient at infinity and the upper restriction.

## References

- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/ParameterClassification.B`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/ParameterClassification.result`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/ParameterClassification.theta`
- Dependency: [D5/S3/Analytic/XuYangMillsRemainder/Result](Result.md)
