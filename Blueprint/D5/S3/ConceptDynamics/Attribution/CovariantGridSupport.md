# Seed budgets for covariant binary calibration

## Abstract

Exact finite seed budgets for covariant binary calibration.

**Definition 1.1 (Covariant binary grid).**

$$\operatorname{CovariantGrid}\left(m, S\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Attribution/CovariantGridSupport.CovariantGrid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural denominator m and finite seed type S, a covariant grid specifies nonnegative real weights with sum one, a weight-preserving involution, and one event of mass k divided by m for each index k from zero through m. The involution takes the event at k to the complement of the event at m minus k.

**Theorem 1.2 (Odd denominators).**

$$\forall m n, \operatorname{Odd}\left(m\right) \Rightarrow ((\exists S:Type [\operatorname{Fintype}\left(S\right)], \operatorname{card}\left(S\right) \le n \land \operatorname{Nonempty}\left(\operatorname{CovariantGrid}\left(m, S\right)\right)) \iff m + 1 \le 2^n)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/CovariantGridSupport.odd_support_budget_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If m is odd and n is a natural budget, a covariant grid exists on at most n seeds if and only if 2 to the power n is at least m plus one. Different levels require different events, so the number of subsets gives the lower bound. Binary place weights, with a final weight chosen to make the sum correct, realize every level. Use the identity involution and pair a lower event with its complement above the midpoint.

**Theorem 1.3 (Even denominators).**

$$\forall q r, 0 < q \Rightarrow ((\exists S:Type [\operatorname{Fintype}\left(S\right)], \operatorname{card}\left(S\right) \le 2 \cdot r \land \operatorname{Nonempty}\left(\operatorname{CovariantGrid}\left(2 \cdot q, S\right)\right)) \iff 2 \cdot q + 1 \le 3^r)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/CovariantGridSupport.even_support_budget_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If q is positive and r is a natural budget for the number of seed pairs, a covariant grid with denominator twice q exists on at most twice r seeds if and only if 3 to the power r is at least twice q plus one.

The midpoint event gives exactly one representative of each two-element orbit. An event's mass is determined by the number of representatives and partners it contains from each orbit. Ternary place weights, with the final weight chosen to make the sum correct, realize every level when each weight is supplied twice. Swap the two seeds in each pair. The midpoint chooses one per pair.

The bounded-digit construction is the complete-partition step of Bachet's weighing problem. The seed weights are inputs to the calibration model.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/CovariantGridSupport.CovariantGrid`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/CovariantGridSupport.even_support_budget_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/CovariantGridSupport.odd_support_budget_iff`
