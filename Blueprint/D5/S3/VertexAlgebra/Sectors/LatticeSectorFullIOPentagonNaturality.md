# Naturality of the finite FullIO pentagon

## Abstract

Naturality of the explicit finite-target FullIO pentagon paths.

**Theorem 1.1 (Short-path naturality).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorFullIOPentagonNaturality.pentagonShortPath_natural`

**Theorem 1.2 (Long-path naturality).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorFullIOPentagonNaturality.pentagonLongPath_natural`

**Theorem 1.3 (Pentagon naturality).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorFullIOPentagonNaturality.fullIO_pentagon_natural`

*Proof.* Machine-checked in Lean as the three declarations above (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Postcomposition by every finite-target module morphism commutes with both
explicit sides of the finite FullIO pentagon. The short side is obtained by
composing the two concrete channel naturality squares. The long side and the
combined statement follow by the finite-target pentagon equality at its two
endpoints. These are finite algebraic identities and do not assert analytic
sewing, convergence, braiding or a physical realization.

## References

- Truth anchors: `D5/S3/VertexAlgebra/Sectors/LatticeSectorFullIOPentagonNaturality.pentagonShortPath_natural`, `D5/S3/VertexAlgebra/Sectors/LatticeSectorFullIOPentagonNaturality.pentagonLongPath_natural`, `D5/S3/VertexAlgebra/Sectors/LatticeSectorFullIOPentagonNaturality.fullIO_pentagon_natural`
- Dependencies: [LatticeSectorFullIOPentagon](LatticeSectorFullIOPentagon.md), [LatticeSectorFullChannelNaturality](LatticeSectorFullChannelNaturality.md)
