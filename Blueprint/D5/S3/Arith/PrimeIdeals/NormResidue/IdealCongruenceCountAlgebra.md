# Lipschitz frontier cover of an orthant-cut region

## Abstract

Lipschitz frontier cover of an orthant-cut region.

**Theorem 1.1 (Lipschitz frontier cover of an orthant-cut region).**

Lean statement: `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountAlgebra.exists_frontier_cover_inter_orthant`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountAlgebra.exists_frontier_cover_inter_orthant` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

Lipschitz frontier cover of an orthant-cut region. If D₀ is bounded with a Lipschitz cube cover of its frontier, then D₀ ∩ orthant (orthant cutting the coordinates g k) also has a Lipschitz cube-covered frontier: frontier (D₀ ∩ O) ⊆ frontier D₀ ∪ (closure D₀ ∩ frontier O) (frontier_inter_subset), the orthant boundary lands in finitely many coordinate hyperplanes, and each bounded hyperplane slice is cube- covered by exists_lipschitz_cube_cover_hyperplane_slab.

## References

- Truth anchor: `D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountAlgebra.exists_frontier_cover_inter_orthant`
- Dependency: [D5/S3/Arith/Lattices/Counting/IdealCongruenceCountRealScale](../../Lattices/Counting/IdealCongruenceCountRealScale.md)
