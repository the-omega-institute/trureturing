# The Original Borcherds Identity with Two Twisted Sources and a Fixed Input

## Abstract

The Original Borcherds Identity with Two Twisted Sources and a Fixed Input

**Theorem 1.1 (Vanishing of the MMV defect).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldMMV.defect_mmv`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldMMV.defect_mmv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D be rank-24 lattice data with unit Gram determinant and positive-definite real Gram form. For any two original negative twisted states u and v and any fixed state a, insert the three states into the original assembled carrier in the order (u, v, a). The Borcherds defect of the assembled field vanishes for every triple of integer indices (p, q, r).

The last-slot exchange uses lower truncation of the assembled modes, divided mode translation for u, and twisted-fixed skew for (v, a). The mode of u on v is fixed, so its iterate with a uses fixed-sector skew. The mode of u on a stays in the negative twisted sector, so the reverse iterate uses the skew law for originalI. Powers of assembled translation on the fixed inclusion are powers of fixed translation transported by that inclusion, which lifts both skew laws to the assembled carrier. See `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.divided_mode_translation`, `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.skew_mv`, `D5/S3/VertexAlgebra/StateField/SkewSymmetry.skew_symmetry`, and `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMMSkew.originalI_skew`.

The exchange expresses the defect as a finite sum of signed divided translates of the defects in the order (u, a, v) at indices (r, q + j, p) for natural j. The MVM law gives zero at each such triple, so every translated summand vanishes. See `D5/S3/VertexAlgebra/StateField/BorcherdsPermutations.defect_swap_last` and `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_mvm`.

## References

- Truth anchor: `D5/S3/VertexAlgebra/StateField/BorcherdsPermutations.defect_swap_last`
- Truth anchor: `D5/S3/VertexAlgebra/StateField/SkewSymmetry.skew_symmetry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMMSkew.originalI_skew`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_mvm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.divided_mode_translation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.skew_mv`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldMMV.defect_mmv`
- Dependency: [D5/S3/VertexAlgebra/StateField/SkewSymmetry](../../StateField/SkewSymmetry.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMMSkew](OriginalMMSkew.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi](OriginalOrbifoldJacobi.md)
