# Padding Residual Action

## Abstract

The actual padding transition erases each emitted letter from the residual.

**Theorem 1.1 (Padding Residual Action).**

$$\operatorname{coordinate}\left(\operatorname{mulVec}\left(\operatorname{W}\left(a, head\right), \operatorname{padding}\left(a, head, r\right)\right), \operatorname{pair}\left(i, k\right)\right) = \operatorname{if}\left(\operatorname{member}\left(i, r\right), \operatorname{coordinate}\left(\operatorname{padding}\left(a, head, \operatorname{erase}\left(r, i\right)\right), k\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingResidualAction.padding_residual_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite alphabet, every multiset a, every chosen head, every nonzero residual r contained in a, every letter i and every memory coordinate k, the letter-i component of W padding(r) equals padding(r.erase(i)) at k if i is present, and equals zero otherwise. The head need not have maximum count.

The proof computes the transition on the actual residual coordinates: head reindexing, tail decrement, the one-tail sink, absent letters and tail-free residuals. For a nonzero residual, the letter-i component is the erased residual when i is present and zero otherwise. The tensor-coordinate identity identifies this action with the prescribed square-root-weighted image. The full attainment proof uses these inner products to preserve every finite complex linear relation before constructing V and U.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingResidualAction.padding_residual_intertwining`
- Dependency: [D5/S3/Quantum/StationaryPreparation/PaddingResidualGram](PaddingResidualGram.md)
- Dependency: [D5/S3/Quantum/StationaryPreparation/PaddingTransition](PaddingTransition.md)
