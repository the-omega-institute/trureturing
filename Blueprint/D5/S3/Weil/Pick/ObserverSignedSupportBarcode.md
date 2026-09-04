# Observer-Dependent Signed-Support Barcode

## Abstract

Observer-dependent signed support is negative exactly on an open orbit interval; under positive masses, the finite count of negative localized weights equals the number of active intervals.

**Definition 1.1 (Observer-dependent signed support).**

Lean statement: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observerSignedSupport`

*Formalization.* `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observerSignedSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The squared observer-height displacement minus the squared transverse displacement.

**Definition 1.2 (Active orbit interval).**

Lean statement: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.orbitActiveAt`

*Formalization.* `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.orbitActiveAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observer lies in the open interval centered at the orbit height with transverse radius.

**Definition 1.3 (Observer-localized atomic weight).**

Lean statement: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observerLocalizedWeight`

*Formalization.* `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observerLocalizedWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positive mass multiplies the observer-dependent signed support.

**Definition 1.4 (Active orbit count).**

Lean statement: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.activeOrbitCount`

*Formalization.* `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.activeOrbitCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite number of orbit intervals containing the observation time.

**Definition 1.5 (Negative localized-weight count).**

Lean statement: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.negativeLocalizedWeightCount`

*Formalization.* `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.negativeLocalizedWeightCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite number of strictly negative localized atomic weights.

**Theorem 1.6 (Signed support is negative exactly on the active interval).**

$$\operatorname{S}(\delta, \gamma, t) < 0 \iff \operatorname{Active}(\delta, \gamma, t)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observer_signed_support_neg_iff_active` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inequality is the difference-of-squares test: the observer-height distance is smaller than the transverse displacement exactly when the signed support is negative.

**Theorem 1.7 (Positive mass preserves the active-interval sign test).**

$$0 < m \implies (\operatorname{w}(m, \delta, \gamma, t) < 0 \iff \operatorname{Active}(\delta, \gamma, t))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observer_localized_weight_neg_iff_active` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict positivity of mass makes multiplication sign-reflecting, so no additional negative direction is introduced by the mass itself.

**Theorem 1.8 (Negative-weight count equals active-interval count).**

$$N^{-} = N_{\operatorname{act}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.negative_localized_weight_count_eq_active_orbit_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two finite filters have pointwise equivalent membership under positive masses, hence their cardinalities agree exactly.

**Theorem 1.9 (Active-orbit existence equals negative-weight existence).**

$$(\exists a, \operatorname{Active}_{a}) \iff (\exists a, w_{a} < 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.exists_active_orbit_iff_exists_negative_localized_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the existential form of the barcode identity. It is still a statement about atomic diagonal weights, not sampled Gram inertia.

**Theorem 1.10 (Signed support at the orbit center).**

$$\operatorname{S}(\delta, \gamma, \gamma) = -\delta^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observer_signed_support_at_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At time gamma, the height displacement vanishes and only the negative transverse square remains.

**Theorem 1.11 (The center is active exactly off axis).**

$$\operatorname{Active}(\delta, \gamma, \gamma) \iff \delta \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.orbit_active_at_center_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The open barcode interval contains its center precisely when its radius is nonzero.

## References

- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.activeOrbitCount`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.exists_active_orbit_iff_exists_negative_localized_weight`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.negativeLocalizedWeightCount`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.negative_localized_weight_count_eq_active_orbit_count`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observerLocalizedWeight`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observerSignedSupport`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observer_localized_weight_neg_iff_active`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observer_signed_support_at_center`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observer_signed_support_neg_iff_active`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.orbitActiveAt`
- Truth anchor: `D5/S3/Weil/Pick/ObserverSignedSupportBarcode.orbit_active_at_center_iff`
- Dependency: [D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel](LocalizedStieltjesNevanlinnaKernel.md)
