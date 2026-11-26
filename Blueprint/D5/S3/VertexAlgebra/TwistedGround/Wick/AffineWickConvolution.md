# Partitioning an occurrence word

## Abstract

Wick expansion for a sum of covariances

**Definition 1.1 (Ordered partitions by position).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickConvolution.partitions`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickConvolution.partitions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose one of two subwords for each position. Both subwords retain the order in the input word, and the list of partitions retains multiplicities.

**Theorem 1.2 (Convolution of Wick evaluations).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickConvolution.wick_add_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickConvolution.wick_add_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two symmetric covariances on a finite type, the Wick evaluation with their sum equals the sum over position partitions. Evaluate the first subword using the correction covariance and zero mean. Evaluate the second with the original covariance and mean. The product rule for the ordered derivatives of the factorized affine Gaussian gives the partition sum.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickConvolution.partitions`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickConvolution.wick_add_covariance`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick](AffineOccurrenceWick.md)
