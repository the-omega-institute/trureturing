# Golden Second-Magnus Sampling

## Abstract

Golden Mellin sample times make second-Magnus curvature descend through whole golden shell shifts.

**Definition 1.1 (Golden Mellin sample time).**

Lean statement: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.goldenSampleTime`

*Formalization.* `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.goldenSampleTime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An integral golden Fourier mode is sent to its vertical Mellin time by multiplying it by the fundamental golden angular frequency.

**Definition 1.2 (Visible golden scale-circle point).**

Lean statement: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.goldenScaleCirclePoint`

*Formalization.* `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.goldenScaleCirclePoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unwrapped logarithmic golden coordinate is projected to the unit additive circle.

**Definition 1.3 (Golden scale Fourier character).**

Lean statement: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.goldenScaleFourierPhase`

*Formalization.* `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.goldenScaleFourierPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integral mode character evaluates the visible golden scale coordinate as a unit complex phase.

**Theorem 1.4 (Positive multiplication becomes circle addition).**

$$\forall x: \mathbb{R}, y: \mathbb{R},\\{}(0 < x) \land (0 < y) \Rightarrow\\{}(\operatorname{goldenScaleCirclePoint}(x \times y) = \operatorname{goldenScaleCirclePoint}(x) + \operatorname{goldenScaleCirclePoint}(y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.golden_scale_circle_point_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication of positive scales adds their unwrapped logarithmic coordinates and therefore adds their visible circle points.

**Theorem 1.5 (Whole golden shells have one visible circle point).**

$$\forall n: \mathbb{N}, x: \mathbb{R},\\{}(0 < x) \Rightarrow\\{}(\operatorname{goldenScaleCirclePoint}((\varphi^{2})^{n} \times x) = \operatorname{goldenScaleCirclePoint}(x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.golden_scale_circle_point_phi_even_pow_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by any natural power of phi squared changes the unwrapped coordinate by an integer and is invisible on the unit additive circle.

**Theorem 1.6 (Golden circle phase equals sampled log-frequency phase).**

$$\forall x: \mathbb{R}, k: \mathbb{Z},\\{}(\operatorname{goldenScaleFourierPhase}(x, k) = \operatorname{fourierPhase}(\operatorname{log}(x), \operatorname{goldenSampleTime}(k))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.golden_scale_fourier_phase_eq_log_frequency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden circle character is exactly the existing Fourier character of log scale evaluated at the corresponding golden Mellin sample time.

**Theorem 1.7 (Golden scale characters have unit norm).**

$$\forall x: \mathbb{R}, k: \mathbb{Z},\\{}(\left\lVert \operatorname{goldenScaleFourierPhase}(x, k) \right\rVert = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.golden_scale_fourier_phase_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sampled phase lies on the complex unit circle for every real scale and integral mode.

**Theorem 1.8 (Golden scale characters are multiplicative).**

$$\forall x: \mathbb{R}, y: \mathbb{R}, k: \mathbb{Z},\\{}(0 < x) \land (0 < y) \Rightarrow\\{}(\operatorname{goldenScaleFourierPhase}(x \times y, k) = \operatorname{goldenScaleFourierPhase}(x, k) \times \operatorname{goldenScaleFourierPhase}(y, k)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.golden_scale_fourier_phase_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At one integral mode, the phase of a positive product is the product of the two phases.

**Theorem 1.9 (Integral modes ignore whole golden shell shifts).**

$$\forall n: \mathbb{N}, x: \mathbb{R}, k: \mathbb{Z},\\{}(0 < x) \Rightarrow\\{}(\operatorname{goldenScaleFourierPhase}((\varphi^{2})^{n} \times x, k) = \operatorname{goldenScaleFourierPhase}(x, k)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.golden_scale_fourier_phase_phi_even_pow_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural whole-shell shift contributes an integral multiple of a full circle turn, so the complex phase is unchanged.

**Theorem 1.10 (Golden sampling realizes the second-Magnus alternant).**

$$\forall x: \mathbb{R}, y: \mathbb{R}, k_{1}: \mathbb{Z}, k_{2}: \mathbb{Z},\\{}(\operatorname{secondMagnusSwapKernel}(\operatorname{log}(x), \operatorname{log}(y), \operatorname{goldenSampleTime}(k_{1}), \operatorname{goldenSampleTime}(k_{2})) = \operatorname{goldenScaleFourierPhase}(x, k_{1}) \times \operatorname{goldenScaleFourierPhase}(y, k_{2}) - \operatorname{goldenScaleFourierPhase}(y, k_{1}) \times \operatorname{goldenScaleFourierPhase}(x, k_{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.second_magnus_kernel_at_golden_samples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At two golden Mellin sample times, the existing second-Magnus kernel is the alternating determinant of four golden scale character values.

**Theorem 1.11 (The sampled kernel descends through shell orbits).**

$$\forall n_{x}: \mathbb{N}, n_{y}: \mathbb{N}, x: \mathbb{R}, y: \mathbb{R}, k_{1}: \mathbb{Z}, k_{2}: \mathbb{Z},\\{}(0 < x) \land (0 < y) \Rightarrow\\{}(\operatorname{secondMagnusSwapKernel}(\operatorname{log}((\varphi^{2})^{n_{x}} \times x), \operatorname{log}((\varphi^{2})^{n_{y}} \times y), \operatorname{goldenSampleTime}(k_{1}), \operatorname{goldenSampleTime}(k_{2})) = \operatorname{secondMagnusSwapKernel}(\operatorname{log}(x), \operatorname{log}(y), \operatorname{goldenSampleTime}(k_{1}), \operatorname{goldenSampleTime}(k_{2}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.golden_second_magnus_shell_orbit_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Independent whole-shell shifts of the two positive scale inputs leave the sampled second-Magnus kernel unchanged.

**Theorem 1.12 (Finite sampled energy descends through channelwise shell orbits).**

$$\forall s, n, C, k_{1}: \mathbb{Z}, k_{2}: \mathbb{Z},\\{}(\forall p, 0 < s_{p}) \Rightarrow\\{}(\operatorname{finiteSecondMagnusEnergy}(p \mapsto \operatorname{log}((\varphi^{2})^{n_{p}} \times s_{p}), C, \operatorname{goldenSampleTime}(k_{1}), \operatorname{goldenSampleTime}(k_{2})) = \operatorname{finiteSecondMagnusEnergy}(p \mapsto \operatorname{log}(s_{p}), C, \operatorname{goldenSampleTime}(k_{1}), \operatorname{goldenSampleTime}(k_{2}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.finite_second_magnus_energy_golden_shell_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying an independent natural whole-shell shift to every positive scale channel preserves the complete finite second-Magnus energy.

## References

- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.finite_second_magnus_energy_golden_shell_invariant`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.goldenSampleTime`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.goldenScaleCirclePoint`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.goldenScaleFourierPhase`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.golden_scale_circle_point_mul`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.golden_scale_circle_point_phi_even_pow_mul`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.golden_scale_fourier_phase_eq_log_frequency`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.golden_scale_fourier_phase_mul`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.golden_scale_fourier_phase_norm`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.golden_scale_fourier_phase_phi_even_pow_mul`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.golden_second_magnus_shell_orbit_invariance`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.second_magnus_kernel_at_golden_samples`
- Dependency: [D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature](../../AgencyHolonomy/SecondMagnusSwapCurvature.md)
- Dependency: [D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling](GoldenVerticalSampling.md)
