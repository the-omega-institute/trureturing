# The discrete center of the shifted Mellin mesh

## Abstract

The shifted Mellin grid has a controlled absolute sum around its central sample.

**Theorem 1.1 (Uniform bound for the symmetric center window).**

$$\frac{\sum_{0\le i<K} \left\lvert \operatorname{sample}\left(\beta, \frac{2}{n}, 1-\frac{i+1}{n}\right)\right\rvert+\left\lvert \operatorname{sample}\left(\beta, \frac{2}{n}, 1\right)\right\rvert+\sum_{0\le i<K} \left\lvert \operatorname{sample}\left(\beta, \frac{2}{n}, 1+\frac{i+1}{n}\right)\right\rvert}{n}\le56 \delta^{\frac{1}{4}}+16 n^{-\frac{1}{4}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedMellinDiscreteCenter.near_center_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n and K be natural numbers, with n positive, and let the real width delta satisfy 0 <= delta <= 1/2 and K/n <= delta. The exponent beta lies in [0,3/4]. The sample is the paired power sample from OccupiedMellinInterior, with actual regularization 2/n.

The two off-center sums run over the positive integer distances i+1 from m=n, once to the left and once to the right. The central term occurs exactly once, even when K is zero; the shift 2/n is retained there. The two sides use monotone integral comparison for the finite negative three-quarter power sum.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedMellinDiscreteCenter.near_center_cutoff`
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedMellinInterior](OccupiedMellinInterior.md)
