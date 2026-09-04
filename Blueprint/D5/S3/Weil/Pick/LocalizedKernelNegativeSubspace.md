# Localized-Kernel Negative Coordinate Subspace

## Abstract

Active observer intervals define a finite coordinate model whose diagonal localized quadratic form is strictly negative away from zero. Its coordinate cardinality is exactly the signed-support barcode count.

**Definition 1.1 (Active orbit subtype).**

Lean statement: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.ActiveOrbit`

*Formalization.* `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.ActiveOrbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Orbit labels whose observer-dependent signed support is negative at the selected time.

**Definition 1.2 (Active-coordinate negative index).**

Lean statement: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.activeCoordinateNegativeIndex`

*Formalization.* `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.activeCoordinateNegativeIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite cardinality of the active-orbit coordinate type.

**Definition 1.3 (Active-orbit filter equivalence).**

Lean statement: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.activeOrbitEquivFiltered`

*Formalization.* `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.activeOrbitEquivFiltered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The active subtype is equivalent to the filtered universal finset used by the barcode count.

**Definition 1.4 (Active-coordinate quadratic form).**

Lean statement: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.activeCoordinateQuadratic`

*Formalization.* `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.activeCoordinateQuadratic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal sum of localized atomic weights times coordinate squares.

**Definition 1.5 (Exact active-coordinate transport).**

Lean statement: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.ExactActiveCoordinateTransport`

*Formalization.* `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.ExactActiveCoordinateTransport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An injective linear realization together with an exact target quadratic readout.

**Theorem 1.6 (The coordinate index equals the barcode count).**

$$activeCoordinateIndexEqualsBarcodeCount$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.active_coordinate_negative_index_eq_active_orbit_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite-cardinality transport through the filter equivalence identifies the two counts exactly.

**Theorem 1.7 (Every active coordinate weight is negative).**

$$positiveMassActiveCoordinateWeightNegative$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.active_coordinate_weight_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive-mass sign theorem applies to the defining property of each active subtype element.

**Theorem 1.8 (The active-coordinate quadratic form is strictly negative).**

$$nonzeroActiveCoordinateVectorHasNegativeQuadraticValue$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.active_coordinate_quadratic_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every summand is nonpositive and a nonzero coordinate supplies one strictly negative summand.

**Theorem 1.9 (Exact transport gives a negative target value).**

$$exactTransportCarriesNegativeCoordinateQuadratic$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.exact_transport_gives_negative_target_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution of the exact readout transfers strict negativity to the target quadratic domain.

**Theorem 1.10 (Exact transport preserves nonzero vectors).**

$$injectiveTransportPreservesNonzero$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.exact_transport_preserves_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Injectivity prevents collapse of a nonzero active coordinate vector in the target space.

## References

- Truth anchor: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.ActiveOrbit`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.ExactActiveCoordinateTransport`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.activeCoordinateNegativeIndex`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.activeCoordinateQuadratic`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.activeOrbitEquivFiltered`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.active_coordinate_negative_index_eq_active_orbit_count`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.active_coordinate_quadratic_neg`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.active_coordinate_weight_neg`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.exact_transport_gives_negative_target_value`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.exact_transport_preserves_nonzero`
- Dependency: [D5/S3/Weil/Pick/ObserverSignedSupportBarcode](ObserverSignedSupportBarcode.md)
