# Complement pairing of residual zero blocks

## Abstract

Complement pairing of residual zero blocks

**Theorem 1.1 (Complement pairing of residual zero blocks).**

$$\forall r \in \mathrm{Nat},\; (6 \le r) \Rightarrow (\frac{\mathrm{card}\left(\mathrm{bad}\left(r\right)\right)}{\mathrm{factorial}\left(2 \cdot r - 1\right)} \le r \cdot \sum_{j\in\mathrm{Icc}\left(2, r - 2\right)}(\mathrm{density}\left(r, j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/PairedResidualBlocks.residual_mass_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bad(r) is the union of all remaining forbidden original-label block events with pair-index sizes from two through r minus two. Counts and factorials are coerced to the rationals in this inequality.

After removing single-pair adjacency events and their complements, the remaining coordinate subsets have cardinalities from two through r-2. Complementation preserves this range and the actual circular event. It has no fixed coordinate subset when r is positive, including at the middle cardinality.

Every occurrence therefore supplies two distinct complementary subset witnesses in the same actual circle. Summing these memberships bounds twice the residual bad-circle count by the full subset-event sum. Exact single-arc contraction and grouping by cardinality turn half of that sum into r times the finite binomial tail. The mass is unconditional; no independence from adjacency avoidance is used.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/PairedResidualBlocks.residual_mass_le`
- Dependency: [D5/S3/Combinatorics/Sequenceability/PairedBinomialTail](PairedBinomialTail.md)
- Dependency: [D5/S3/Combinatorics/Sequenceability/PairedCircleEvents](PairedCircleEvents.md)
