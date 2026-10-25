# A finite uniform quantitative bound for paired C3 Good orders

## Abstract

A finite uniform quantitative bound for paired C3 Good orders

**Theorem 1.1 (A finite uniform quantitative bound for paired C3 Good orders).**

$$\forall r \in \mathrm{Nat},\; (12 \le r) \Rightarrow ((\mathrm{factorial}\left(2 \cdot r\right) \cdot \mathrm{lowerFraction}\left(r\right) \le \mathrm{card}\left(\mathrm{goodOrders}\left(r\right)\right)) \land ((0 < \mathrm{lowerFraction}\left(r\right)) \land (0 < \mathrm{card}\left(\mathrm{goodOrders}\left(r\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/PairedQuantitativeOrdering.quantitative_good_orders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

GoodOrders(r) is the actual finite set of original signed coordinate-label orders satisfying Good. LowerFraction(r) is exactly the explicit rational polynomial fraction defined below; no count or numerical premise is assumed.

For every natural r at least twelve, take the original distinct labels plus and minus the r coordinate basis vectors in C3^r. The theorem counts actual permutations of this alphabet with coefficient one and original group addition. Every nonempty proper contiguous interval must have nonzero sum; the full word alone is exempt.

The lower bound is (2r)! times (8r^3-123r^2+388r-45)/(3(2r-1)(2r-3)(2r-5)), and the fraction is strictly positive. The proof combines actual simultaneous circular block contractions, the third finite Bonferroni estimate, exact complement pairing, and the finite symmetric binomial tail. At r=12+s the numerator is 8s^3+165s^2+892s+723. The zero-total seam bridge and free rotation fibers identify the result with the actual rooted Good orders.

This improves understanding of event overlap where the first-moment estimate fails. The corresponding words are known as rooted connected chord diagrams after forgetting coordinate names and signs. Mahmoud and Yeats, Connected Chord Diagrams and the Combinatorics of Asymptotic Expansions, arXiv:2010.06550v2, give a stronger asymptotic expansion for that established class. No novelty or priority for this finite certificate is claimed. This result concerns this paired alphabet only; unrestricted AM and arbitrary-subset sequenceability are not resolved.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/PairedQuantitativeOrdering.quantitative_good_orders`
- Dependency: [D5/S3/Combinatorics/CircularWords/CircularOrderCount](../CircularWords/CircularOrderCount.md)
- Dependency: [D5/S3/Combinatorics/Sequenceability/PairedNoAdjacencyEstimate](PairedNoAdjacencyEstimate.md)
- Dependency: [D5/S3/Combinatorics/Sequenceability/PairedResidualBlocks](PairedResidualBlocks.md)
- Dependency: [D5/S3/Combinatorics/Sequenceability/ZeroTotalCircleGood](ZeroTotalCircleGood.md)
