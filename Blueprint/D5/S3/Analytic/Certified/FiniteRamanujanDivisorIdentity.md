# Finite Ramanujan Divisor Identity

## Abstract

The normalized sum of finite Ramanujan phases over the divisors of d is the indicator that d divides n.

**Definition 1.1 (The finite Ramanujan phase sum).**

$$\forall q, n \in \mathbb{N}, \operatorname{ramanujanSum}\left(q, n\right) = \sum_{0 \leq a < q, \operatorname{Coprime}\left(a, q\right)} \operatorname{exp}\left(2 \cdot \pi \cdot i \cdot \frac{a \cdot n}{q}\right).$$

*Formalization.* `D5/S3/Analytic/Certified/FiniteRamanujanDivisorIdentity.ramanujanSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural q and n, ramanujanSum q n is exactly the finite sum of exp(2 pi i a n / q) over natural residues a below q that are coprime to q. In particular, the phase carrier is not replaced by an arithmetically equivalent definition.

**Theorem 1.2 (Normalized Ramanujan sums reconstruct the divisor indicator).**

$$\forall d, n \in \mathbb{N}, 0 < d \Rightarrow \mathbf{1}_{{\{d \mid n\}}} = \frac{1}{d} \cdot \sum_{q \mid d} \operatorname{ramanujanSum}\left(q, n\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Certified/FiniteRamanujanDivisorIdentity.divisorIndicator_eq_normalized_sum_ramanujanSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural d and natural n, the indicator of d dividing n equals one over d times the sum of c_q(n) over all positive divisors q of d. This is formula (4) in the finite reconstruction argument.

The proof first constructs the coprime-index bijection from the source phases to primitive q-th roots. Primitive roots of all orders q dividing d partition the d-th roots of unity; the complete root sum is then d when d divides n and zero otherwise.

This module does not prove the von Mangoldt equality, the weighted finite phase expansion, or independence of that expansion from tau. Those remain separate obligations.

## References

- Truth anchor: `D5/S3/Analytic/Certified/FiniteRamanujanDivisorIdentity.divisorIndicator_eq_normalized_sum_ramanujanSum`
- Truth anchor: `D5/S3/Analytic/Certified/FiniteRamanujanDivisorIdentity.ramanujanSum`
