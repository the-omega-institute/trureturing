# Observer Signed-Support Barcode

## Abstract

Observer-dependent negative support is exactly the open reflected-orbit barcode.

**Definition 1.1 (Observer-dependent signed support).**

Lean statement: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observerSignedSupport`

*Formalization.* `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observerSignedSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support coordinate is the squared height mismatch minus the squared transverse displacement.

**Definition 1.2 (Active orbit interval).**

Lean statement: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.orbitActiveAt`

*Formalization.* `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.orbitActiveAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An orbit is active when the observation parameter lies strictly inside its reflected interval.

**Definition 1.3 (Localized signed weight).**

Lean statement: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observerLocalizedWeight`

*Formalization.* `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observerLocalizedWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positive atomic mass multiplies the observer-dependent signed support.

**Definition 1.4 (Active barcode count).**

Lean statement: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.activeOrbitCount`

*Formalization.* `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.activeOrbitCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite count records all active reflected-orbit intervals.

**Definition 1.5 (Negative localized-weight count).**

Lean statement: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.negativeLocalizedWeightCount`

*Formalization.* `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.negativeLocalizedWeightCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite count records all strictly negative mass-times-support weights.

**Theorem 1.6 (Negative support is equivalent to interval activity).**

Lean statement: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observer_signed_support_neg_iff_active`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observer_signed_support_neg_iff_active` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic inequality is exactly the absolute-value interval condition.

**Theorem 1.7 (Positive masses preserve the barcode count).**

Lean statement: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.negative_localized_weight_count_eq_active_orbit_count`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.negative_localized_weight_count_eq_active_orbit_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strictly positive masses preserve every support sign, so the two finite filters are equal.

**Theorem 1.8 (Active orbit existence equals negative-weight existence).**

Lean statement: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.exists_active_orbit_iff_exists_negative_localized_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.exists_active_orbit_iff_exists_negative_localized_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointwise sign equivalence is lifted to finite existential detection.

## References

- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observerSignedSupport`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.orbitActiveAt`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observerLocalizedWeight`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.activeOrbitCount`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.negativeLocalizedWeightCount`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observer_signed_support_neg_iff_active`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.negative_localized_weight_count_eq_active_orbit_count`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.exists_active_orbit_iff_exists_negative_localized_weight`
