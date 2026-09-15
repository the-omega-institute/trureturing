# The OEIS A245786 Subsequence Conjecture

## Abstract

The seventh listed A245786 member is not an A216793 gcd record.

**Definition 1.1 (Membership in A245786).**

$$\forall n \in \mathbb{N},\; (IsMember\left(n\right)) \Leftrightarrow (\exists z \in \mathbb{Z},\; \frac{(n: \mathbb{Q})}{(\left(\sigma_{0}\right)\left(n\right): \mathbb{Q})} + \frac{(\left(\sigma_{1}\right)\left(n\right): \mathbb{Q})}{(n: \mathbb{Q})} = z)$$

*Formalization.* `D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.IsMember` (`✓ std3`).

*Citation.* Jaroslav Krizek (2014). *OEIS A245786, Numbers n such that k(n) = (n/tau(n) + sigma(n)/n) is an integer*. URL: <https://oeis.org/A245786>.

*Commentary.*

Here sigma sub zero is tau, the divisor-count function, and sigma sub one is the divisor-sum function. Membership means that the displayed rational sum is an integer.

**Definition 1.2 (The A216793 gcd record predicate).**

$$\forall n \in \mathbb{N},\; (IsRecord\left(n\right)) \Leftrightarrow (\forall m \in \mathbb{N},\; 0 < m \Rightarrow \left(m < n \Rightarrow \gcd\left(\left(\sigma_{1}\right)\left(m\right), m\right) < \gcd\left(\left(\sigma_{1}\right)\left(n\right), n\right)\right))$$

*Formalization.* `D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.IsRecord` (`✓ std3`).

*Citation.* Jaroslav Krizek (2014). *OEIS A245786, Numbers n such that k(n) = (n/tau(n) + sigma(n)/n) is an integer*. URL: <https://oeis.org/A245786>.

*Commentary.*

At a natural n, the gcd of sigma sub one of n with n must be strictly larger than the corresponding gcd at every positive smaller m.

**Definition 1.3 (Krizek's subsequence conjecture).**

$$(claim) \Leftrightarrow (\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(IsMember\left(n\right) \Rightarrow IsRecord\left(n\right)\right))$$

*Formalization.* `D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.claim` (`✓ std3`).

*Citation.* Jaroslav Krizek (2014). *OEIS A245786, Numbers n such that k(n) = (n/tau(n) + sigma(n)/n) is an integer*. URL: <https://oeis.org/A245786>.

*Commentary.*

The conjecture says that every positive A245786 member is an A216793 gcd record.

**Theorem 1.4 (The conjecture fails at n = 275890944).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a245786-integrality-gcd-record-refutation` (refuted) by `D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a245786-integrality-gcd-record-refutation","declaration_gid":"D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jaroslav Krizek (2014). *OEIS A245786, Numbers n such that k(n) = (n/tau(n) + sigma(n)/n) is an integer*. URL: <https://oeis.org/A245786>.

*Commentary.*

At N = 275890944, tau(N) = 288 and sigma(N) = 919636480, so N/tau(N) + sigma(N)/N = 957958. Its gcd value is 91963648. For the smaller M = 142990848, sigma(M) = 571963392 = 4M and the gcd value is M itself. Thus N is a member but not a record.

## References

- Truth anchor: `D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.IsMember`
- Truth anchor: `D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.IsRecord`
- Truth anchor: `D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.claim`
- Truth anchor: `D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.result`
