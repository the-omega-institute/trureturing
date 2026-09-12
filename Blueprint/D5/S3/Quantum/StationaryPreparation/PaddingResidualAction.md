# Padding Residual Action

## Abstract

The actual padding transition preserves the prescribed image inner products.

**Theorem 1.1 (Padding Residual Action).**

$$\operatorname{inner}\left(\operatorname{image}\left(a, head, r\right), \operatorname{image}\left(a, head, s\right)\right) = \operatorname{inner}\left(\operatorname{phi}\left(a, head, r\right), \operatorname{phi}\left(a, head, s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingResidualAction.prescribed_image_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the finite alphabet be nonempty, let a have arbitrary natural capacities, and choose a maximum-count head. For every pair of legal residuals r and s, image(a,head,r) and image(a,head,s) have the same inner product as the corresponding normalized padding vectors. The zero residual emits head into the common sink.

The proof computes the transition on the actual residual coordinates: head reindexing, tail decrement, the one-tail sink, absent letters and tail-free residuals. For a nonzero residual, the letter-i component is the erased residual when i is present and zero otherwise. The tensor-coordinate identity identifies this action with the prescribed square-root-weighted image. The full attainment proof uses these inner products to preserve every finite complex linear relation before constructing V and U.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingResidualAction.prescribed_image_gram`
- Dependency: [D5/S3/Quantum/StationaryPreparation/PaddingResidualGram](PaddingResidualGram.md)
- Dependency: [D5/S3/Quantum/StationaryPreparation/PaddingTransition](PaddingTransition.md)
