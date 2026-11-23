# Central contractions and surviving creators

## Abstract

Wick expansion of the lowering word at one puncture

**Definition 1.1 (Evaluated central pair weight).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMWickLowering.pairWeight`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMWickLowering.pairWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate the central pair polynomial at a complex lowering parameter and take its constant oscillator coefficient.

**Theorem 1.2 (Partition into contraction endpoints and surviving creators).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMWickLowering.eval_word_partition`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMWickLowering.eval_word_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a lattice with unit Gram determinant, a finite label type with an assigned oscillator index at each label, and any word and complex parameter, the evaluated lowering word is a sum over ordered partitions of its positions. The first subword contributes the zero-mean Wick value of the evaluated pair weights, embedded as a constant oscillator polynomial. The second contributes the product of evaluated creators. The recursion deletes paired positions individually, so repeated labels and modes retain their multiplicities.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMWickLowering.eval_word_partition`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMWickLowering.pairWeight`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial](../../HalfFock/OriginalHalfCurrentWickPolynomial.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickConvolution](../Wick/AffineWickConvolution.md)
