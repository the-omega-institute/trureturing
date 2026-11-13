# Full neutral action before projection

## Abstract

LatticeCosetCanonicalNeutral

**Theorem 1.1 (neutral_action_invariance).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalNeutral.neutral_action_invariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalNeutral.neutral_action_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive-definite original D, arbitrary external rank and integral B, every label d, every original acting state h, every original input v and integer m, Y of the neutral injection of h acts on the d injection of v as the d injection of the exact action D (B*d) h at mode m on v. The acting h may have arbitrary original charge. This holds before projection. Here the charged ground transports and arbitrary oscillator source recursion are used in mixed_integer.

**Theorem 1.2 (compressed_neutral).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalNeutral.compressed_neutral`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalNeutral.compressed_neutral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same complete scope, compressing the neutral source field in the d sector is exactly the existing dual-coset action with raw label B*d, on every state and mode. It identifies both ordered native Borcherds products in mixed_integer.

Classical conventions: Bakalov--Kac, math/0402315v1, section 4.1. Native residue and conformal sources retain Scott Carnahan and Kalle Kytölä attributions. No mathematical novelty, physical realization, categorical fusion completion or string completion is claimed. The original rank may be zero; all external-rank statements also include zero.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalNeutral.compressed_neutral`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalNeutral.neutral_action_invariance`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner](LatticeCosetCanonicalIntertwiner.md)
