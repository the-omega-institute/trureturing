# Frequency Vectors of the Original Signed Columns

## Abstract

Frequency Vectors of the Original Signed Columns

The finite binomial contiguous identity realizes internal frequency multiplication as an actual Hilbert vector. The predecessor at positive mode zero is the negative zero label; no boundary is discarded.

**Definition 1.1 (externalParameter).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.externalParameter`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.externalParameter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The parameter is p+1/2 for true and -p-1/2 for false, for each natural p.

**Definition 1.2 (predecessor).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.predecessor`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.predecessor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predecessor lowers the parameter by one: positive zero goes to negative zero, positive successor to the previous positive mode, and negative p to negative p+1.

**Definition 1.3 (frequencyVector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.frequencyVector`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.frequencyVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vector is alpha times the difference of the original external vector and its actual predecessor.

**Theorem 1.4 (binomial_frequency).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.binomial_frequency`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.binomial_frequency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For both signed labels and all natural p,s, s times the actual external binomial equals alpha times its contiguous predecessor difference.

**Theorem 1.5 (frequencyVector_apply).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.frequencyVector_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.frequencyVector_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Throughout the complex unit disk, every coordinate of the actual frequencyVector is n+1 times the original externalColumn at n.

**Theorem 1.6 (externalVector_negative_zero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.externalVector_negative_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.externalVector_negative_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Throughout the complex unit disk, the actual negative external zero vector is exactly minus sourceFamily 1.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.binomial_frequency`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.externalParameter`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.externalVector_negative_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.frequencyVector`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.frequencyVector_apply`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.predecessor`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose](OriginalGaussianBilinearTranspose.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation](OriginalGaussianSourceEvaluation.md)
