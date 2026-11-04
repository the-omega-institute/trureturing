# Original tensor unrestricted Borcherds identity

## Abstract

Original tensor unrestricted Borcherds identity

Actual signed tensor locality and actual Hahn truncation give a high-r vanishing discrepancy. The native homogeneous integer iterate gives the p=0 seed. The supported Pascal recurrence propagates to nonnegative p and, by descending cutoff distance and induction on negative magnitude, to every integer p,q,r. Four actual parity components combine with finite supports to give the mixed-state law. The proof adapts the pinned BcGhostBorcherds high-index and descent argument, retaining Scott Carnahan vertexAlg Apache-2.0 attribution (revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea); see Matsuo--Nagatomo hep-th/9706118v1 Proposition 1.5.5 and Theorem 5.4.1. No literature novelty claim is made.

**Theorem 1.1 (Original tensor carrier, all states, all three integer indices).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostBorcherds.borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostBorcherds.borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary lattice data D and arbitrary mixed states a,b,c in the original State D, with the original Y D and parity D, the theorem proves the full Borcherds identity for every integer p,q,r. All four action families have genuine finite support. With a0=(a+Pa)/2 and a1=(a-Pa)/2, the reverse term is Y(b) after Y(a0) plus Y(Pb) after Y(a1), multiplied by (-1)^r. No rank, Gram, nondegeneracy, H, homogeneity, field closure, Jacobi, Borcherds or BRST square-zero premise occurs. The identity is on the coupled lattice/ghost tensor itself; no ghost-carrier transport is used. Quotient identities, BRST cohomology, fusion, string theory and AdS/CFT completion are outside this theorem.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostBorcherds.borcherds`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostSignedBorcherds](LatticeMatterGhostSignedBorcherds.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateFieldIterate](LatticeMatterGhostStateFieldIterate.md)
