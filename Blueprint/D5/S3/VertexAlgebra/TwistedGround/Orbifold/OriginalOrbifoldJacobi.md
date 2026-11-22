# Signed Jacobi Identities for the Original Orbifold Field

## Abstract

Signed Jacobi Identities for the Original Orbifold Field

The fixed lattice vertex algebra supplies the all-fixed Jacobi law and fixed-sector skew. The identities with three twisted states and with two twisted sources acting on a fixed state remain open for the assembled field.

**Theorem 1.1 (Divided translation of the source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.divided_state_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.divided_state_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Iterating the rank-24 coefficient derivative on the source gives the signed binomial coefficient for each divided power.

**Theorem 1.2 (Divided translation of the input).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.divided_mode_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.divided_mode_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Iterating the rank-24 covariance relation moves translation across a mode as a finite binomial sum.

**Theorem 1.3 (Twisted source and fixed input).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.skew_mv`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.skew_mv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original right coefficient is the signed sum of divided translates of the reversed fixed-action modes.

**Theorem 1.4 (Fixed source and twisted input).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.skew_vm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.skew_vm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing the finite signed translation sum collapses it to its zeroth diagonal by the binomial identity.

**Theorem 1.5 (Two fixed sources and a twisted input).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_vvm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_vvm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed-fixed-twisted Borcherds identity makes the signed coefficient defect vanish at every integer index.

**Theorem 1.6 (Fixed source followed by two twisted states).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_vmm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_vmm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In rank 24, the original mixed coefficient law gives the three sums after inclusion into the fixed sector. Lower truncation bounds the signed sum that uses the fixed action on the last twisted state.

**Theorem 1.7 (Twisted state in the middle of two fixed states).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_vmv`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_vmv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In rank 24, divided input translation and twisted-fixed skew exchange the last two slots. Every resulting term has the fixed-fixed-twisted order.

**Theorem 1.8 (Twisted state followed by two fixed states).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_mvv`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_mvv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In rank 24, divided source translation and twisted-fixed skew exchange the first two slots and reduce to the fixed-twisted-fixed identity.

**Theorem 1.9 (Fixed state in the middle of two twisted states).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_mvm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_mvm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In rank 24, the first-slot exchange reduces the twisted-fixed-twisted identity to the fixed-twisted-twisted law.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_mvm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_mvv`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_vmm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_vmv`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.defect_vvm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.divided_mode_translation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.divided_state_translation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.skew_mv`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldJacobi.skew_vm`
- Dependency: [D5/S3/VertexAlgebra/StateField/BorcherdsPermutations](../../StateField/BorcherdsPermutations.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation](OriginalOrbifoldTranslation.md)
