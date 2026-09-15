# Padding Residual Gram

## Abstract

The concrete residual-coordinate overlap is the minimum-head word multiplicity.

**Theorem 1.1 (Padding Residual Gram).**

$$\operatorname{inner}\left(\operatorname{padding}\left(a, head, b\right), \operatorname{padding}\left(a, head, c\right)\right) = \operatorname{if}\left(\operatorname{tailOcc}\left(head, b\right) = \operatorname{tailOcc}\left(head, c\right), \operatorname{M}\left(\operatorname{headSlice}\left(head, b, \operatorname{min}\left(\operatorname{count}\left(b, head\right), \operatorname{count}\left(c, head\right)\right)\right)\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingResidualGram.padding_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite alphabet, arbitrary natural capacities encoded by a, every head, and every pair b and c of submultisets of a, the inner product of padding(b) and padding(c) is determined by their common coordinates. A nonzero tail contributes exactly at its whole-tail coordinate and at head indices bounded by the residual head count. The common coordinates of two residuals stop at their minimum head count.

Equal tails give the corresponding minimum-head word multiplicity, and distinct tails give zero. The last-tail masses telescope, including the sink and tail-free cases. After normalization, comparable residuals have the square-root multiplicity ratio times their tail moment; reversed comparisons use complex conjugation and incomparable pairs vanish.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingResidualGram.padding_inner`
- Dependency: [D5/S3/Quantum/StationaryPreparation/PaddingTransition](PaddingTransition.md)
