# Reflected Zero Modes and Phase Flattening

## Abstract

A normalized complex zero mode splits into a real radial channel and a unit phase channel, while functional reflection, conjugation, and same-height mirror remain distinct involutions.

**Definition 1.1 (Signed displacement from the critical line).**

Lean statement: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.criticalDisplacement`

*Formalization.* `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.criticalDisplacement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displacement is the real part of the spectral point minus the frozen critical abscissa.

**Definition 1.2 (Normalized zero generator).**

Lean statement: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.normalizedZeroGenerator`

*Formalization.* `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.normalizedZeroGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

After the uniform damping shift cancels, the generator has real part minus the critical displacement and imaginary part equal to the ordinate.

**Definition 1.3 (Normalized zero mode).**

Lean statement: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.normalizedZeroMode`

*Formalization.* `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.normalizedZeroMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The auxiliary mode is the complex exponential of the normalized generator times a real mode parameter.

**Definition 1.4 (Phase-flattened zero mode).**

Lean statement: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.phaseFlattenedZeroMode`

*Formalization.* `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.phaseFlattenedZeroMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplication by the inverse ordinate phase removes the common unit-modulus rotation while retaining the radial channel.

**Theorem 1.5 (Skewness is exactly critical-line location).**

$$\operatorname{conj}(\operatorname{normalizedZeroGenerator}(rho)) = -\operatorname{normalizedZeroGenerator}(rho) \Longleftrightarrow \operatorname{Re}(rho) = criticalAbscissa.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.normalized_zero_generator_skew_iff_critical_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized generator is skew under complex conjugation exactly when its real part vanishes, which is exactly critical-line location.

**Theorem 1.6 (The zero mode factors into radial and phase channels).**

$$\operatorname{normalizedZeroMode}(rho, t) = \operatorname{radialZeroMode}(rho, t) \cdot \operatorname{commonZeroPhase}(rho, t).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.normalized_zero_mode_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The radial factor carries the horizontal displacement and the phase factor carries the ordinate. The phase factor has unit norm in a separate Lean theorem.

**Theorem 1.7 (Phase flattening leaves the radial mode).**

$$\operatorname{phaseFlattenedZeroMode}(rho, t) = \operatorname{radialZeroMode}(rho, t).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.phase_flattened_zero_mode_eq_radial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse phase exactly cancels the common ordinate rotation, with no approximation or branch choice.

**Theorem 1.8 (Functional reflection acts as mode-time reversal).**

$$\operatorname{normalizedZeroMode}(\operatorname{functionalReflection}(rho), t) = \operatorname{normalizedZeroMode}(rho, -t).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.zero_mode_functional_reflection_time_reversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map rho to one minus rho negates both generator coordinates. On the auxiliary exponential mode this equals reversing the mode parameter.

**Theorem 1.9 (Conjugation reverses the frequency channel).**

$$\operatorname{normalizedZeroMode}(\operatorname{conj}(rho), t) = \operatorname{conj}(\operatorname{normalizedZeroMode}(rho, t)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.zero_mode_conjugation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complex conjugation preserves the radial rate and reverses the ordinate phase. It is distinct from functional reflection and from same-height mirror.

**Theorem 1.10 (Same-height mirror gives reciprocal radial branches).**

$$\operatorname{phaseFlattenedZeroMode}(rho, t) \cdot \operatorname{phaseFlattenedZeroMode}(\operatorname{criticalLineMirror}(rho), t) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.phase_flattened_critical_line_mirror_reciprocal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After phase flattening, rho and one minus conjugate rho have opposite radial rates, so their two modes multiply to one.

**Theorem 1.11 (Stored reflection and conjugation commute).**

$$\operatorname{reflection}(\operatorname{conjugation}(n)) = \operatorname{conjugation}(\operatorname{reflection}(n)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.zeroData_reflection_conjugation_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Duplicate-free zero enumeration turns equality of the two same-height mirror images into equality of the two index permutations.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.criticalDisplacement`
- Truth anchor: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.normalizedZeroGenerator`
- Truth anchor: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.normalizedZeroMode`
- Truth anchor: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.normalized_zero_generator_skew_iff_critical_line`
- Truth anchor: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.normalized_zero_mode_factorization`
- Truth anchor: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.phaseFlattenedZeroMode`
- Truth anchor: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.phase_flattened_critical_line_mirror_reciprocal`
- Truth anchor: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.phase_flattened_zero_mode_eq_radial`
- Truth anchor: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.zeroData_reflection_conjugation_commute`
- Truth anchor: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.zero_mode_conjugation`
- Truth anchor: `D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.zero_mode_functional_reflection_time_reversal`
