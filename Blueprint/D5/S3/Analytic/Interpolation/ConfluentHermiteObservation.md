# Uniform noisy recovery from Hermite observations

## Abstract

Noisy recovery of weighted coefficients from confluent Hermite data.

**Definition 1.1 (Nonconstant Hermite prefix differences).**

Lean statement: `D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.hermiteTail`

*Formalization.* `D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.hermiteTail` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Carl de Boor (2005). *Divided Differences*. URL: <https://arxiv.org/abs/math/0502036>.

*Commentary.*

For each order j from 1 to m, use the first j + 1 occurrences of the supplied list of m + 1 nodes. At a node of multiplicity k, the interpolant of degree at most j matches derivatives of orders 0 through k - 1 taken within the measurement interval. Its coefficient of degree j is the observation of order j.

**Theorem 1.2 (The scalar coefficient estimate).**

Lean statement: `D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.hermiteTail_noisy_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.hermiteTail_noisy_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Carl de Boor (2005). *Divided Differences*. URL: <https://arxiv.org/abs/math/0502036>.

*Commentary.*

Fix positive integers m and r and an interval [lo, hi] with 0 < lo < hi. Let p have the coefficient vector v of length m. On this interval assume F(x) = K + x^r p(x) + E(x), where E is C^m within the interval and each derivative of order j is bounded in absolute value by B_j for j from 1 to m.

There is a constant delta > 0 depending only on m, r and the interval. For every ordered tuple of m + 1 nodes in the interval, delta times the sup norm of v is at most the sup norm of the nonconstant prefix differences of F plus the maximum of B_j / j!. The nodes may coincide in any pattern, including at an endpoint.

Interpolation is additive on the smooth inputs, and positive-order coefficients of the constant interpolant vanish. For the weighted polynomial, each prefix interpolant is the remainder by the corresponding monic nodal product, so its top coefficient equals the corresponding Newton coefficient. Use `D5/S3/Analytic/Interpolation/ConfluentPositiveSampling.weightedNewtonTail_uniform_lower` for uniform recovery of v. Repeated Rolle steps give the factorial-scaled remainder bound for each prefix.

**Definition 1.3 (Two-port Hermite observations).**

Lean statement: `D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.matrixHermiteTail`

*Formalization.* `D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.matrixHermiteTail` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Carl de Boor (2005). *Divided Differences*. URL: <https://arxiv.org/abs/math/0502036>.

*Commentary.*

Apply the scalar observation to each entry of a real two-by-two matrix function, giving one matrix per prefix order.

**Theorem 1.4 (The two-port operator norm estimate).**

Lean statement: `D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.matrixHermiteTail_noisy_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.matrixHermiteTail_noisy_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Carl de Boor (2005). *Divided Differences*. URL: <https://arxiv.org/abs/math/0502036>.

*Commentary.*

Assume the same decomposition and smoothness entrywise, and bound the Euclidean operator norm of the derivative matrix at order j by B_j throughout the interval. The maximum operator norm of the coefficient matrices is bounded by a constant times the sum of the maximum observed prefix operator norm and the maximum of B_j / j!. With the scalar lower-bound constant delta, the proof gives 2 / delta by bounding each entry and then the Frobenius norm.

For the slow expansion on the physical observation window, take r = 3 and [lo, hi] = [1/2, 1]. For a difference of expansions the coefficient vector has entries T^k times the corresponding slow coefficient differences, and K is the difference of the integration constants. The observation estimate uses the expansion and derivative budgets as hypotheses.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.hermiteTail`
- Truth anchor: `D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.hermiteTail_noisy_recovery`
- Truth anchor: `D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.matrixHermiteTail`
- Truth anchor: `D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.matrixHermiteTail_noisy_recovery`
- Truth anchor: `D5/S3/Analytic/Interpolation/ConfluentPositiveSampling.weightedNewtonTail_uniform_lower`
- Dependency: [D5/S3/Analytic/Interpolation/ConfluentPositiveSampling](ConfluentPositiveSampling.md)
