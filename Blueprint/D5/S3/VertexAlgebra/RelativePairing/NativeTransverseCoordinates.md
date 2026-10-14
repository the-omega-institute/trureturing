# Native Transverse Coordinates

## Abstract

Native finite coefficients recover the original relative transverse energy-sector states.

The source is the actual complex Finsupp on TransverseDownIndex at a fixed lattice charge and integer level. Its indices are native oscillator monomials with zero occupation on both distinguished frame axes and empty polarized ghost word. No finite occupation cutoff is imposed. The state map uses the original coordinateSub and down. Both frame inverse equations and, for energy support, both Gram inverse equations remain explicit.

**Theorem 1.1 (Coefficient recovery).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.coordinates_downState`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.coordinates_downState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

coordinates restricts the actual nativeCoefficients linear map along the injective native index powers to (powers, empty). Applying it to downState recovers every finite complex coefficient family exactly. The restriction is a Finsupp comapDomain, so finite support is retained.

**Theorem 1.2 (Actual projector in native coordinates).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.projector_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.projector_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P_native is extended through the original charge-sector finite basis expansion. The native coefficient at an index survives precisely when its actual kappa occupation is zero. No replacement projector or supplied transverse-membership premise occurs.

**Theorem 1.3 (Reconstruction of every relative projector-fixed state).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.downState_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.downState_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a state in originalEnergySector fixed by the actual P and killed by the original B(0), every nonzero native coefficient has zero occupation on the two axes. kappa_zero_iff restricts the polarized ghost word to the epsilon site; native_relative_support excludes that site. Thus the ghost word is genuinely empty. nativeT0_support_level places the oscillator monomial in the exact TransverseDownIndex. A support-surjective native index embedding and sum_comapDomain then reconstruct the original state, not merely an abstract isomorphic carrier.

**Theorem 1.4 (Existing reduced inputs are the native state map).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.energyInput_state`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.energyInput_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full-state value of energyTransverseDownCombination is exactly downState. This consumed interface identifies the existing finite HPL inputs with the actual coefficient representation.

**Theorem 1.5 (Literal oscillator tensor down).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.downState_tensor`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.downState_tensor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual state is Finsupp.single at the chosen charge of transverseDownOscillator, tensor the original down ghost. These coordinate consequences do not assert positivity or any no-ghost or radical conclusion.

## References

- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.coordinates_downState`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.downState_coordinates`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.downState_tensor`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.energyInput_state`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.projector_coordinates`
- Dependency: [D5/S3/VertexAlgebra/OriginalQEnergyInclusionPairing](../OriginalQEnergyInclusionPairing.md)
