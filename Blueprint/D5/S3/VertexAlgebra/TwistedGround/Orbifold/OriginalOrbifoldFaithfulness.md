# Faithfulness of the Original Fixed-Sector Action

## Abstract

Faithfulness of the Original Fixed-Sector Action

**Theorem 1.1 (Recovering the fixed vacuum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldFaithfulness.originalI_three_eq_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldFaithfulness.originalI_three_eq_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In rank 24, the original mode of index three takes a pair of negative twisted states of weight two to the fixed-sector vacuum after rescaling the second state. Its vacuum scalar is the same nonzero normalized coefficient used in the Leech vacuum channel.

**Theorem 1.2 (Detecting fixed states with twisted modes).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldFaithfulness.fixedParitySlice_faithful`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldFaithfulness.fixedParitySlice_faithful` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every mode of a fixed state vanishes on the negative twisted sector, the mixed Jacobi identity forces its creation on the recovered vacuum to vanish.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldFaithfulness.fixedParitySlice_faithful`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldFaithfulness.originalI_three_eq_vacuum`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSourceModeTransport](OriginalSourceModeTransport.md)
