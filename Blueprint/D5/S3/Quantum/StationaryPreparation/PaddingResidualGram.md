# Padding Residual Gram

## Abstract

The concrete residual-coordinate overlap gives the complete normalized Gram matrix.

**Theorem 1.1 (Padding Residual Gram).**

$$\operatorname{gram}\left(\operatorname{phi}\left(a, head\right)\right) = \operatorname{G}\left(a, head\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingResidualGram.phi_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite alphabet, arbitrary natural capacities encoded by a, and every head, the Gram matrix of the legal normalized padding vectors is G(a,head). A nonzero tail contributes exactly at its whole-tail coordinate and at head indices bounded by the residual head count. The common coordinates of two residuals stop at their minimum head count.

Equal tails give the corresponding minimum-head word multiplicity, and distinct tails give zero. The last-tail masses telescope, including the sink and tail-free cases. After normalization, comparable residuals have the square-root multiplicity ratio times their tail moment; reversed comparisons use complex conjugation and incomparable pairs vanish.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingResidualGram.phi_gram`
- Dependency: [D5/S3/Quantum/StationaryPreparation/PaddingTransition](PaddingTransition.md)
