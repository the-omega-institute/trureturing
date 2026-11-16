# FullIO channel naturality

## Abstract

Naturality of the actual FullIO channel transport for finite target-module morphisms.

**Theorem 1.1 (FullIO channel naturality).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorFullChannelNaturality.fullChannel_natural`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorFullChannelNaturality.fullChannel_natural` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite target-module morphism `g : Hom D M N`, the actual FullIO channel transport commutes with postcomposition by `g`. The proof unfolds the channel through the incoming universal equivalence, uses its existing naturality, and applies the concrete incoming reassociation map. This is a finite algebraic naturality statement; it does not assert analytic sewing, convergence, a full pentagon, or a physical realization.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorFullChannelNaturality.fullChannel_natural`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport](LatticeSectorChannelTransport.md)
