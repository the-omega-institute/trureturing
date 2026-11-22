# Local rewrites for the negative twisted sector

## Abstract

Finite Borcherds rewrites on the actual negative twisted sector.

**Theorem 1.1 (Expansion of a source C2 letter).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddModeStraightening.minusTwo_mem_of_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddModeStraightening.minusTwo_mem_of_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite iterate at p = 0 and r = -2 expands one source C2 letter into pairs whose mode indices sum to the original index minus two.

**Theorem 1.2 (Adjacent mode swap).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddModeStraightening.swap_mem_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddModeStraightening.swap_mem_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite commutator at r = 0 expresses the difference of adjacent orders through nonnegative products in the fixed source.

**Theorem 1.3 (Elimination of a repeated mode index).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddModeStraightening.duplicate_mem_of_shorter_and_larger`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddModeStraightening.duplicate_mem_of_shorter_and_larger` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the finite normal product, isolate the repeated pair in the first sum for a negative index and in the second sum with exchanged inputs for a nonnegative index. Every other pair has the same index sum and a strictly larger square sum.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddModeStraightening.duplicate_mem_of_shorter_and_larger`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddModeStraightening.minusTwo_mem_of_pairs`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddModeStraightening.swap_mem_iff`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField](OriginalOrbifoldField.md)
