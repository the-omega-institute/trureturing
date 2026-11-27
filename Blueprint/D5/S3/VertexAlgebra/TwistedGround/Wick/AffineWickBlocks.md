# Restriction to the occurrence word

## Abstract

Wick evaluation on independent covariance blocks

**Theorem 1.1 (Covariances agreeing along the word).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickBlocks.wick_congr_on`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickBlocks.wick_congr_on` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the same mean, two covariances give the same Wick value on a word whenever they agree on every pair of labels occurring in it. The condition is inherited by the shorter words in the recurrence.

**Theorem 1.2 (Factorization across two blocks).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickBlocks.wick_block`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickBlocks.wick_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite label type, a symmetric covariance that vanishes between opposite values of a Boolean block predicate has a zero-mean Wick value equal to the product of the two values on the filtered subwords. In the covariance convolution, a position assigned to the wrong block has no eligible pair, so only the partition selected by the predicate can contribute.

**Theorem 1.3 (Factorization over a finite set of blocks).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickBlocks.wick_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickBlocks.wick_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite label type, take a symmetric covariance that vanishes between different slots and a finite set of slots with decidable equality containing the slot of each word entry. The zero-mean Wick value is the product of the values on the subwords filtered by each slot. Induction on the slot set applies the two-block formula to separate one slot at a time.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickBlocks.wick_block`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickBlocks.wick_blocks`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickBlocks.wick_congr_on`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickConvolution](AffineWickConvolution.md)
