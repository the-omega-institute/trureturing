# Strict Growth of the Optimal Real-law Slope

## Abstract

The minimum ratio of dyadic sampling cost to least atom mass grows strictly with the label count.

**Theorem 1.1 (Strict growth with the number of labels).**

$$\operatorname{alpha}\left(1\right) = 0 \land \operatorname{alpha}\left(2\right) = 2 \land (\forall m: \mathbb{N}, (3 \le m) \to \operatorname{alpha}\left((m - 1)\right) < \operatorname{alpha}\left(m\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a strictly positive normalized real law p on m labels, the dyadic cost is the sum over depths d of the unassigned floor remainder divided by 2^d. The function alpha is the infimum of this cost divided by the smallest mass, as defined by CarryGraphCriticalAttainment. The domain contains all such real laws, without a rationality or finite-depth restriction.

A single label has zero cost. For two labels, the cost is at least one and the smallest mass is at most one half. The uniform two-label law has cost one and attains ratio two.

Take an attaining law with at least three labels. Merging two atoms never increases any floor remainder. If the smallest atom is unique, merging it with another atom strictly raises the new minimum mass. If two atoms have the same smallest mass, their first positive binary digit produces a strict carry one depth earlier, so merging them strictly reduces the convergent cost sum. In each case the new law has a strictly smaller ratio, proving the strict inequality for consecutive label counts.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment](CarryGraphCriticalAttainment.md)
