# Difference-one straightening

## Abstract

For a positive-definite lattice, degreewise generation by homogeneous representatives and minus-two products puts homogeneous mode words in the span of strictly increasing representative words.

**Theorem 1.1 (Terminating straightening of homogeneous words).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddDifferenceOneSpanning.word_mem_strictSpan`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddDifferenceOneSpanning.word_mem_strictSpan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three inductions use total source weight, word length, and the deficit of the square sum from an upper bound at fixed index sum. Sort large-index terms and apply truncation at the seed before comparing square sums.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddDifferenceOneSpanning.word_mem_strictSpan`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](../../LatticeActualLZeroGrading.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddModeStraightening](OddModeStraightening.md)
