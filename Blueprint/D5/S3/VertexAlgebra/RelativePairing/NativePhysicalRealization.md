# Native Physical Realization

## Abstract

The genuine finite original-Q HPL maps identify native down coefficients with the literal relative ghost-one physical image.

The lattice has rank 26. Both Gram inverse equations, both frame inverse equations, a null longitudinal direction, its nonzero chosenP at the fixed charge, distinct axes, the literal null and adapted-partner rows, both dual-row identities and the exact shell equation chosenH plus integer level minus one equals zero are retained. There is no supplied physical-membership, inverse, isometry or no-ghost premise. The algebraic descent does not require star-fixed rows. The original neutral obstruction and the global string and AdS/CFT objectives are not conclusions of this construction.

**Theorem 1.1 (Actual inclusion has relative ghost degree one).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.inclusion_physical`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.inclusion_physical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map is the existing energyReducedInclusion applied to the existing finite native transverse-down combination. The on-shell transferred differential vanishes by its actual computation; the genuine finite transfer chain law proves the original Q-cycle equation. The actual B0 transfer compatibility propagates the native empty-word B0 kernel through the full finite correction. The original ghost-number commutator of the finite correction inverse propagates the degree-one equation from down. The energy-sector membership is the inclusion's actual subtype, not an assumed readout.

**Theorem 1.2 (Native coefficients of the actual finite projection).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.projection_coordinate_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.projection_coordinate_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

physicalProjection first applies the original energyTransferProjection to the literal physical representative, then restricts its actual polynomial/ghost basis coefficients. The B0 compatibility and the native coordinate reconstruction theorem identify the projected state exactly. projection_ghost_one follows from this literal down-state reconstruction; no spectral representative assumption is used.

**Theorem 1.3 (Ambient original boundaries are killed).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.physicalProjection_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.physicalProjection_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the original ambient Q-boundary relation, ambient_boundary_sector_preimage supplies a preimage in the actual charge-energy sector. The genuine projection chain law and actual zero transferred differential annihilate its finite projection. Thus quotientProjection descends through physicalBoundaries, and imageProjection uses the established imageEquiv only to address the literal submodule physicalImage of OriginalCohomology.

**Theorem 1.4 (Literal representative recovery).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.imageProjection_representative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.imageProjection_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On imageRepresentative of a literal physical cycle, imageProjection is exactly its actual finite HPL projection followed by native coefficient extraction. The image map itself uses OriginalBoundaries.mkQ; its actual kernel homotopy, not a replacement boundary relation, proves equality of representatives.

**Definition 1.5 (Two-sided native physical equivalence).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.nativePhysicalEquiv`

*Formalization.* `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.nativePhysicalEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward linear map is nativeImage and the inverse is imageProjection. imageProjection_nativeImage uses the original finite retract and exact native coefficient recovery. nativeImage_imageProjection uses the actual Q-homotopy and original ambient boundaries to recover every literal physical image class. Both directions apply to arbitrary finite complex inputs and arbitrary classes in the literal image, without an externally supplied bijection.

**Theorem 1.6 (Exact negative original oscillator form).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.nativeImage_form`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.nativeImage_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the two longitudinal rows explicitly star-fixed, imageForm_recovery and the existing energyReducedInclusion_transverse_down_normalization identify the literal image form on any two native coefficient families with the negative actual fockForm of their coordinateSub oscillators. The sign comes from the unchanged down ghost and inserted C(0). This proves an exact sesquilinear identity, not positivity, nondegeneracy, a radical description or a full no-ghost theorem.

## References

- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.imageProjection_representative`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.inclusion_physical`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.nativeImage_form`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.nativePhysicalEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.physicalProjection_boundary`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization.projection_coordinate_recovery`
- Dependency: [D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates](NativeTransverseCoordinates.md)
- Dependency: [D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent](OriginalPhysicalDescent.md)
