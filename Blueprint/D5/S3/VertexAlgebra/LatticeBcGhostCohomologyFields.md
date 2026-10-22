# Scope

## Abstract

Actual BRST quotient fields and their algebraic laws.

The pointwise truncated quotient modes construct genuine Laurent-series-valued complex linear state fields. The vacuum and translation are images of the actual tensor vacuum and translation. The available concrete StateFieldVertexAlgebra record is ungraded and does not match these signed laws; no ungraded VOA label is substituted. A conformal super-vertex record, fusion category, CFT realization, complete string theory, and AdS/CFT bridge remain separate obligations.

**Theorem 1.1 (Actual quotient field coefficients).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.field_mode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.field_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integer coefficient is exactly the constructed bilinear quotient product.

**Theorem 1.2 (Creation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.creation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.creation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The minus-one mode on the actual descended vacuum recovers the quotient state.

**Theorem 1.3 (Vacuum modes).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.vacuum_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.vacuum_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only the minus-one vacuum mode survives; every other vacuum mode vanishes.

**Theorem 1.4 (Original Q commutes with actual translation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.Q_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.Q_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual mixed Q derivation, vacuum closure, and intrinsic translation-as-mode equality establish this relation on the full original carrier.

**Theorem 1.5 (Descended covariance).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient translation satisfies the complete integer-mode covariance law.

**Theorem 1.6 (Descended state derivative).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The field of a translated quotient state has the actual differentiated modes.

For the original lattice tensor state space, suppose H * gramComplex D = 1 and gramComplex D * H = 1. Write T for the actual tensor translation, Q for the original charge, and B(-1) for its original antighost mode. The all-integer ward_identity at mode -1 gives Q * B(-1) + B(-1) * Q = M(-1) + G(-1). The actual translation_original identifies the right side with T under both inverse equations. Thus T = Q * B(-1) + B(-1) * Q on every original state, with no charge-sector, energy, or parity restriction.

If v belongs to OriginalCycles = ker Q, the same equality gives T v = Q(B(-1) v). The explicit original boundary preimage is B(-1) v; it is not assumed to be a cycle. Since OriginalBoundaries is the pullback of range Q along the cycle inclusion, cycleTranslation v is in precisely that denominator. The existing translation_mk and induction on the actual mkQ classes therefore give translation = 0 as an endomorphism of OriginalCohomology, not merely on selected representatives.

For arbitrary quotient classes a and b and any integer n distinct from -1, apply the existing derivative law at exactly n + 1: product(n + 1, translation a, b) = -((n + 1) : Complex) * product(n, a, b). The left side is zero because translation = 0. Characteristic zero and n + 1 != 0 make the scalar nonzero, so product(n, a, b) = 0. This applies equally to positive and negative integer modes and to mixed charge, ghost-number, and parity superpositions; no homogeneous representative is required.

By field_mode, every normalized coefficient of the actual stateField(a) is its original product(n, a). Consequently stateField(a) is literally VertexOperator.of_coeff of the coefficient function that is product(-1, a) at Laurent degree zero and zero at every other degree. Its sole possible normalized coefficient is the real minus-one product; this calculation does not assert that the product or any class is nonzero.

These quotient identities require both Gram inverse equations but not rank 26. Without a proved square-zero charge, the algebraic definition is only ker Q modulo the intersection of ker Q with range Q. For the genuine critical BRST interpretation, additionally retain D.rank = 26: LatticeBcGhostBrstNilpotence.nilpotent then proves Q * Q = 0, and original_image_in_cycles proves range Q is contained in OriginalCycles. The same translation and constant-field calculation thus applies to the actual original critical complex. This is an application of the existing Ward and field laws, not a new canonical theorem or an originality claim; it establishes no noncritical nilpotence, nonzero conformal structure, unitarity, fusion realization, string dynamics, or global spacetime/AdS geometry.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.Q_translation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.covariance`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.creation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.derivative`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.field_mode`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields.vacuum_product`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi](LatticeBcGhostCohomologyJacobi.md)
