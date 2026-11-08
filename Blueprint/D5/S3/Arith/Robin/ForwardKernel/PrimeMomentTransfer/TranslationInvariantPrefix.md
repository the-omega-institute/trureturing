# Translation-invariant prefix identity

## Abstract

Prefix rectangles of a symmetric translation-invariant kernel are determined by three square sums.

**Definition 1.1 (Rectangle prefix sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TranslationInvariantPrefix.kernelRectSum`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TranslationInvariantPrefix.kernelRectSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the kernel over the integer prefixes from one to m and from one to n.

**Definition 1.2 (Square prefix sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TranslationInvariantPrefix.kernelSquareSum`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TranslationInvariantPrefix.kernelSquareSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the kernel over the square of the integer prefix from one to m.

**Theorem 1.3 (Rectangle prefix identity).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TranslationInvariantPrefix.prefix_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TranslationInvariantPrefix.prefix_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a symmetric translation-invariant kernel, the rectangle prefix sum equals one half of the sum of the two corresponding square prefix sums minus the square prefix sum at the distance between their lengths.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TranslationInvariantPrefix.kernelRectSum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TranslationInvariantPrefix.kernelSquareSum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TranslationInvariantPrefix.prefix_identity`
