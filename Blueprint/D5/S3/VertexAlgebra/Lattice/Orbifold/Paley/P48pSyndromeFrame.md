# The P48p Pairing Frame

## Abstract

The concrete P48p frame reduces norm-two exclusion to a ternary syndrome check.

**Theorem 1.1 (The catalogue frame has norm twelve).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pSyndromeFrame.p48pFrameRows_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pSyndromeFrame.p48pFrameRows_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral row computations prove that the frame Gram matrix is twelve times the identity in the Nebe–Sloane P48p catalogue basis.

**Theorem 1.2 (Norm-two exclusion from the short syndromes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pSyndromeFrame.p48p_catalogue_rootless`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pSyndromeFrame.p48p_catalogue_rootless` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact pairing identity and column congruences permit the ternary syndrome criterion on the actual catalogue lattice. The remaining premise is injectivity on words of weight at most three.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pSyndromeFrame.p48pFrameRows_orthogonal`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pSyndromeFrame.p48p_catalogue_rootless`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate](../P48qGramCertificate.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/NormTwoTernarySyndrome](NormTwoTernarySyndrome.md)
