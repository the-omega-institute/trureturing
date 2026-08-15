# Green-Class Window Total Variation

## Abstract

Total variation of a finite naming-window law lies below the sum of its coordinate variations and above every single coordinate variation.

**Theorem 1.1 (Window total variation is bounded by the coordinate sum).**

$$\operatorname{TV}(\operatorname{windowLaw}(p), \operatorname{windowLaw}(q)) \le \sum_{i} \operatorname{TV}(p_{i}, q_{i}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowTotalVariation.totalVariation_windowLaw_le_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative normalized coordinate laws, change the product one coordinate at a time. The triangle inequality bounds the endpoint distance by the sum of the distances along this finite hybrid path.

At an insertion step, all unchanged factors are collected outside the absolute coordinate difference. Finite sum-product factorization makes their total mass one, leaving exactly twice the coordinate total variation before the defining one-half factor is applied.

Induction over the coordinate finset therefore gives the displayed upper bound, including the empty-window case. No equality claim or strictness witness is included.

**Theorem 1.2 (Each coordinate total variation is bounded by the window).**

$$\operatorname{TV}(p_{i}, q_{i}) \le \operatorname{TV}(\operatorname{windowLaw}(p), \operatorname{windowLaw}(q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowTotalVariation.totalVariation_le_totalVariation_windowLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Project a window assignment to coordinate i through the deterministic indicator channel. The channel is nonnegative and row-stochastic because exactly one output letter agrees with the selected coordinate.

Normalization of every coordinate outside i collapses the channel output to p_i, and similarly to q_i. Total-variation data processing then gives the lower half of the window sandwich.

**Theorem 1.3 (Green-class window total variation has the coordinate-sum bound).**

$$\operatorname{TV}(\operatorname{windowLaw}(\operatorname{coordLaw}(mu)), \operatorname{windowLaw}(\operatorname{coordLaw}(nu))) \le \sum_{i} \operatorname{TV}(\operatorname{coordLaw}(mu, i), \operatorname{coordLaw}(nu, i)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/GreenClassWindowTotalVariation.totalVariation_greenClass_window_le_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A probability measure on the finite alphabet gives a nonnegative normalized real coordinate law by singleton evaluation and conversion from extended nonnegative reals.

Applying the general window upper bound to the coordinates selected by the finite set S and reindexing the subtype sum yields the Green-class specialization.

## References

- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowTotalVariation.totalVariation_greenClass_window_le_sum`
- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowTotalVariation.totalVariation_le_totalVariation_windowLaw`
- Truth anchor: `D5/S3/Entropy/NamingWindow/GreenClassWindowTotalVariation.totalVariation_windowLaw_le_sum`
- Dependency: [D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy](GreenClassWindowEntropy.md)
- Dependency: [D5/S3/TotalVariation/DataProcessing](../../TotalVariation/DataProcessing.md)
- Dependency: [D5/S3/TotalVariation/Metric](../../TotalVariation/Metric.md)
