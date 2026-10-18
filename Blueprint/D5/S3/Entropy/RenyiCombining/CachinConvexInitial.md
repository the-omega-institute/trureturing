# Initial Jets of the Riccati Quotient

## Abstract

The analytic bias quotient has exact initial derivatives through order four.

For n different from zero, desingularize the odd power difference by its divided difference at zero. Mathlib's binomial power series and its analytic divided-difference theorem provide a smooth quotient near zero. The initial data are computed from that exact series, using the Leibniz rule on the quotient identity.

**Definition 1.1 (Divided power difference).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.H`

*Formalization.* `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H_n(t) = dslope(s ↦ (1+s)^n − (1−s)^n, 0, t)

At zero, dslope uses the derivative, so H_n(0)=2n.

**Definition 1.2 (Even power sum).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.K`

*Formalization.* `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K_n(t) = (1+t)^n + (1−t)^n

This even real-power expression has value two at zero.

**Definition 1.3 (Desingularized bias quotient).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q`

*Formalization.* `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q_n(t) = n K_n(t)/H_n(t)

The quotient is total as a real function, and analytic near zero when n is nonzero.

**Theorem 1.4 (Initial denominator).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.H_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.H_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

H_n(0) = 2n

The first coefficient of the odd power difference is 2n.

**Theorem 1.5 (Analytic extension).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_analyticAt_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_analyticAt_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

n ≠ 0 → AnalyticAt R Q_n 0

The denominator at zero is 2n, hence is nonzero under the stated hypothesis.

**Theorem 1.6 (Initial quotient).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

n ≠ 0 → Q_n(0) = 1

The quotient of n times the initial numerator two and the denominator 2n is one.

**Theorem 1.7 (Agreement with the punctured formula).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

t ≠ 0 → Q_n(t) = nt ((1+t)^n+(1−t)^n)/((1+t)^n−(1−t)^n)

Away from zero, the divided difference is the power difference divided by t.

**Theorem 1.8 (Exact initial derivatives).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_jets`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_jets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

n ≠ 0 → Q_n'(0)=0 ∧ Q_n''(0)=2(n^2−1)/3 ∧ Q_n'''(0)=0 ∧ Q_n''''(0)=−8(1−n^2)(4−n^2)/15

The binomial coefficients give the denominator and numerator derivatives. Differentiating Q_n H_n=n K_n through order four determines these four derivatives. For 0 < n <= 1/4 the second and fourth derivatives are strictly negative.

**Theorem 1.9 (Local derivative chain).**

Lean statement: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_local_derivatives`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_local_derivatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

n ≠ 0 → ∃a>0, (∀t∈[0,a], ∀k, HasDerivAt (D^k Q_n) (D^(k+1) Q_n(t)) t) ∧ ContinuousAt (D^4 Q_n) 0

Analyticity holds throughout a neighborhood of zero, so all iterated derivatives exist there. These certificates are consumed by the square-root reparametrization and its local sign argument.

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.H`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.H_zero`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.K`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_analyticAt_zero`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_eq`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_jets`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_local_derivatives`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexInitial.Q_zero`
