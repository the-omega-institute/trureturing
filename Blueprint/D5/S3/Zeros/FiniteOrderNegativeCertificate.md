# Finite-Order Negative Certificate

## Abstract

A nontrivial positive-order family with positive weights and zero weighted sum has a negative finite-order coefficient.

**Theorem 1.1 (A zero weighted sum has a negative finite-order certificate).**

$$\forall J \in \operatorname{Nat}\left(\right) \to \operatorname{Real}\left(\right), w \in \operatorname{Nat}\left(\right) \to \operatorname{Real}\left(\right),\; \left(\operatorname{positiveWeights}\left(w\right) \land \left(\operatorname{summablePositiveOrders}\left(w, J\right) \land \left(\operatorname{weightedSumPositiveOrders}\left(w, J\right) = 0 \land \operatorname{nontrivialPositiveOrders}\left(J\right)\right)\right)\right) \Rightarrow \left(\exists m \in \operatorname{Nat}\left(\right),\; 1 \le m \land \operatorname{apply}\left(J, m\right) < 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/FiniteOrderNegativeCertificate.exists_finite_order_negative_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be a real coefficient family on positive integer orders and let w be strictly positive there. If the weighted family is summable, its sum is zero, and at least one coefficient is nonzero, then some finite order m >= 1 has J(m) < 0.

The source derives coefficient nontriviality from a nonzero entire function. That analytic carrier and its series identity are absent from the atom, so the formal statement exposes the exact nontriviality premise needed by the series argument.

Pinned Mathlib's Summable.tsum_pos proves the contradiction: if every coefficient were nonnegative, a nonzero coefficient and a positive weight would make the zero total strictly positive.

A companion Lean theorem witnesses sharpness with unit weights, J(1) = -1, J(2) = 1, and all remaining coefficients zero. Thus the hypotheses and exact zero-sum boundary are jointly inhabited.

## References

- Truth anchor: `D5/S3/Zeros/FiniteOrderNegativeCertificate.exists_finite_order_negative_certificate`
