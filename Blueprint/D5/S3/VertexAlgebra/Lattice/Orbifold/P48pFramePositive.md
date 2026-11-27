# Positive Definiteness of the P48p Gram Matrix

## Abstract

The checked norm-twelve frame proves positive definiteness of the P48p catalogue Gram matrix.

**Theorem 1.1 (The catalogue Gram matrix is positive definite).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48pFramePositive.p48pGram_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48pFramePositive.p48pGram_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over the reals, let G be the Nebe–Sloane P48p catalogue Gram matrix and U the rows of the existing orthogonal norm-twelve frame. The checked pairing matrix F = GUᵀ satisfies UF = 12I, so F is invertible. The same certificate gives FFᵀ = 12G. Thus G = (1/12)FFᵀ is positive definite, using only the existing frame.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48pFramePositive.p48pGram_posDef`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48pSyndromeFrame](P48pSyndromeFrame.md)
