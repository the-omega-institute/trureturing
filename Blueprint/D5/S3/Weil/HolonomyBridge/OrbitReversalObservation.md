# Orbit Reversal Observation

## Abstract

The existing Weil orbit parity channels realize the hidden-idempotent classification of visible negation.

**Definition 1.1 (pairSwap).**

Lean statement: `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.pairSwap`

*Formalization.* `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.pairSwap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exchange the actual pair of spectral readouts.

**Definition 1.2 (oddObservation).**

Lean statement: `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.oddObservation`

*Formalization.* `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.oddObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The frozen odd spectral channel, with its existing normalization.

**Theorem 1.3 (fixedPart eq even channel).**

Lean statement: `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.fixedPart_eq_even_channel`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.fixedPart_eq_even_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hidden fixed part is exactly the existing even spectral channel.

**Theorem 1.4 (weil visible negation lift).**

Lean statement: `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.weil_visible_negation_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.weil_visible_negation_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same general lift theorem applies to the actual odd Weil readout. Its entire fixed component is invisible to that readout.

**Theorem 1.5 (off line orbit in reversal coordinates).**

Lean statement: `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.off_line_orbit_in_reversal_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.off_line_orbit_in_reversal_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source's actual off-line orbit has the same energy decomposition in the reversal-observation coordinates. This consumes the original theorem.

## References

- Truth anchor: `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.fixedPart_eq_even_channel`
- Truth anchor: `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.oddObservation`
- Truth anchor: `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.off_line_orbit_in_reversal_coordinates`
- Truth anchor: `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.pairSwap`
- Truth anchor: `D5/S3/Weil/HolonomyBridge/OrbitReversalObservation.weil_visible_negation_lift`
- Dependency: [D5/S3/Observer/Reversal/VisibleNegationLifts](../../Observer/Reversal/VisibleNegationLifts.md)
- Dependency: [D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition](OffLineOrbitParityDecomposition.md)
