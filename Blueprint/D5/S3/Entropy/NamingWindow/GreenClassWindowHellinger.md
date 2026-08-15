# Green-Class Window Hellinger Structure

## Abstract

Finite naming-window Bhattacharyya affinity factors across coordinates, giving an exact product-defect formula and a coordinate-sum bound for squared Hellinger distance.

**Theorem 1.1 (Window affinity is the product of coordinate affinities).**

$$\operatorname{BC}(\operatorname{windowLaw}(p), \operatorname{windowLaw}(q)) = \prod_{i} \operatorname{BC}(p_{i}, q_{i}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowHellinger.bhattacharyya_windowLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every coordinate radicand p_i(a)q_i(a) is nonnegative, the square root of the window product is the product of the coordinate square roots. Finite sum-product factorization then gives one affinity factor per coordinate.

The hypothesis follows the asymmetric signature of Real.sqrt_prod. No normalization is required for this multiplicative identity.

**Theorem 1.2 (Window Hellinger square is an exact product defect).**

$$H^{2}(\operatorname{windowLaw}(p), \operatorname{windowLaw}(q)) = 2 \times (1-\prod_{i} (1-\frac{H^{2}(p_{i}, q_{i})}{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowHellinger.hellingerSq_windowLaw_product_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative normalized coordinate laws, each coordinate affinity is one minus half its squared Hellinger distance. Window affinity multiplicativity therefore turns the probability Hellinger identity into the displayed product defect.

The product law is exact, including the empty coordinate family. It records the interaction term that prevents squared Hellinger distance from being additive on independent windows.

**Theorem 1.3 (Window Hellinger square is bounded by the coordinate sum).**

$$H^{2}(\operatorname{windowLaw}(p), \operatorname{windowLaw}(q)) \le \sum_{i} H^{2}(p_{i}, q_{i}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowHellinger.hellingerSq_windowLaw_le_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Half of every coordinate Hellinger square lies in the unit interval. Induction over the finite coordinate set proves that one minus the product of the complementary factors is at most their sum.

Applying that elementary product-defect inequality to the exact window formula yields the coordinate-sum upper bound. Equality is not claimed; the omitted mixed defect terms are generally nonzero.

## References

- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowHellinger.bhattacharyya_windowLaw`
- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowHellinger.hellingerSq_windowLaw_le_sum`
- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowHellinger.hellingerSq_windowLaw_product_defect`
- Dependency: [D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy](GreenClassWindowEntropy.md)
- Dependency: [D5/S3/TotalVariation/BhattacharyyaProduct](../../TotalVariation/BhattacharyyaProduct.md)
- Dependency: [D5/S3/TotalVariation/HellingerDivergence](../../TotalVariation/HellingerDivergence.md)
