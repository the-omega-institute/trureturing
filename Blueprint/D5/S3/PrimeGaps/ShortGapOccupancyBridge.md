# Two prime hits give a consecutive gap

## Abstract

Two prime hits give a consecutive gap.

**Theorem 1.1 (Two prime hits give a consecutive gap).**

$$\forall H\in \operatorname{Finset}\left(Nat\right), B,n\in Nat, {\forall h\in H,h\le B}\land2\le \operatorname{primeTranslateOccupancy}\left(H, n\right)\Rightarrow\operatorname{BoundedConsecutivePrimeGapAt}\left(B, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/ShortGapOccupancyBridge.two_prime_occupancy_yields_consecutive_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the inherited two-hit theorem from PR 5236. For every finite natural offset set H and natural B,n, the two hypotheses are the bound on every offset and at least two prime hits at n. The conclusion retains the same interval [n,n+B], consecutive primality, and the explicit gap bound.

## References

- Truth anchor: `D5/S3/PrimeGaps/ShortGapOccupancyBridge.two_prime_occupancy_yields_consecutive_gap`
- Dependency: [D5/S3/Analytic/PrimeProducts/FiniteLocalResidueBlockingCriterion](../Analytic/PrimeProducts/FiniteLocalResidueBlockingCriterion.md)
