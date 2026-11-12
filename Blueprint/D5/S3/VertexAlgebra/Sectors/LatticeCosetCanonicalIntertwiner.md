# Complete rational Hahn lattice-coset fields

## Abstract

LatticeCosetCanonicalIntertwiner

**Definition 1.1 (shift).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.shift`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.shift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational offset is the original inverse-Gram pairing of external labels through the integral cross block B. External rank is arbitrary, including zero; the ambient block has lower-right block zero and need not be positive or nonsingular.

**Definition 1.2 (intertwiner).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.intertwiner`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.intertwiner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full native compressedField is reindexed by the order embedding k maps to shift plus k in rational Hahn exponents. It is complex linear in both complete original carrier arguments. No prescribed ground coefficient, charge law or exponent-support predicate is added to an intertwiner law.

**Theorem 1.3 (field_coeff).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.field_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.field_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, finite external rank, integral B, labels a,b, complete original states u,v and integer k, the reindexed field coefficient at shift+k is exactly the original compressed coefficient at k. It identifies the reindexed modes and the ground coefficient.

**Theorem 1.4 (field_coeff_off).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.field_coeff_off`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.field_coeff_off` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every rational exponent outside the full image shift+Z the field coefficient is zero for all u,v. It gives source linearity and the off-coset Jacobi and derivative laws.

**Theorem 1.5 (mode_integer).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.mode_integer`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.mode_integer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At rational mode m-shift for every integer m, the canonical field is the actual native compressed mode m on every source and input. The raw exponent convention is minus mode minus one. It transfers integer Jacobi and translation identities to the rational exponent coset.

**Theorem 1.6 (ground_coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.ground_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.ground_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At raw exponent shift, the canonical field on both original vacuum states has coefficient exactly vacuum, the old-charge-zero oscillator-constant vector. The original external ground pairing is zero and its cocycle sign is one. Taking its constant coordinate gives ground_scalar.

**Theorem 1.7 (ground_scalar).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.ground_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.ground_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The old-charge-zero oscillator-constant coordinate of that actual raw-shift coefficient is exactly one. This is derived from the native field, not an assumption. It proves nonvanishing and the normalization of groundEvaluation in additive fusion.

**Theorem 1.8 (intertwiner_ne_zero).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.intertwiner_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.intertwiner_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original lattice and every finite external rank, B and external a,b, the source-linear full Hahn intertwiner is nonzero. It makes scalarInclusion injective, giving scalarEquiv its right inverse.

Classical conventions: Bakalov--Kac, math/0402315v1, section 4.1. Native residue and conformal sources retain Scott Carnahan and Kalle Kytölä attributions. No mathematical novelty, physical realization, categorical fusion completion or string completion is claimed. The original rank may be zero; all external-rank statements also include zero.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.field_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.field_coeff_off`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.ground_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.ground_scalar`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.intertwiner`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.intertwiner_ne_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.mode_integer`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner.shift`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeCosetOperatorCorrection](LatticeCosetOperatorCorrection.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoro](LatticeDualCosetVirasoro.md)
