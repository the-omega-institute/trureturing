# Reflected-Pair Curvature Rayleigh Intertwiner

## Abstract

The frozen off-line curvature dipole is the normalized even-channel quadratic readout of a canonical two-dimensional reflected generator.

**Definition 1.1 (The detuned reflected generator).**

Lean statement: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.detunedReflectedGenerator`

*Formalization.* `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.detunedReflectedGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two-by-two complex generator is i tau times the identity plus delta times the frozen Pauli-X coupling. It carries spectral detuning and radial reflection in one finite operator.

**Definition 1.2 (The even channel).**

Lean statement: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.evenChannelState`

*Formalization.* `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.evenChannelState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The standard first basis vector is the branch-symmetric readout channel.

**Definition 1.3 (The even-channel negative-square readout).**

Lean statement: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.evenChannelNegativeSquareReadout`

*Formalization.* `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.evenChannelNegativeSquareReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The repository Hermitian form reads minus the square of the finite generator on the even channel.

**Definition 1.4 (The even-channel energy readout).**

Lean statement: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.evenChannelEnergyReadout`

*Formalization.* `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.evenChannelEnergyReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same Hermitian form reads the positive Gram operator A-star A on the even channel.

**Definition 1.5 (The normalized curvature Rayleigh readout).**

Lean statement: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.normalizedCurvatureRayleighReadout`

*Formalization.* `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.normalizedCurvatureRayleighReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Twice the signed negative-square readout is divided by the square of the positive energy readout.

**Definition 1.6 (The coarse center-polarity kernel).**

Lean statement: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.centerCurvaturePolarityKernel`

*Formalization.* `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.centerCurvaturePolarityKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Zero splitting selects the zero one-point kernel. Every nonzero split selects the canonical oneNegativeKernel already owned by the Pick library.

**Theorem 1.7 (The normalized readout is the rational dipole profile).**

$$\forall delta: \mathbb{R}, tau: \mathbb{R}, \operatorname{normalizedCurvatureRayleighReadout}(delta, tau) = 2 \cdot \frac{(tau^{2} - delta^{2})}{((tau^{2} + delta^{2})^{2})}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.normalized_curvature_rayleigh_readout_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative-square numerator is tau squared minus delta squared, while the positive energy is tau squared plus delta squared.

**Theorem 1.8 (The analytic dipole and finite Rayleigh chart agree).**

$$\forall delta: \mathbb{R}, gamma: \mathbb{R}, t: \mathbb{R}, 0 < delta \Rightarrow \operatorname{offLineCurvature}(delta, gamma, t) = \operatorname{normalizedCurvatureRayleighReadout}(delta, t - gamma).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.off_line_curvature_rayleigh_intertwiner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The already frozen second normal derivative of the reflected logarithmic potential equals the normalized finite readout at detuning t minus gamma.

**Theorem 1.9 (Hyperbolic monodromy is negative center curvature).**

$$\forall rho: \mathbb{C}, \operatorname{IsHyperbolic}(\operatorname{offlineZeroMonodromy}(rho)) \iff \operatorname{normalizedCurvatureRayleighReadout}(\operatorname{criticalDisplacement}(rho), 0) < 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.offline_zero_monodromy_hyperbolic_iff_negative_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen hyperbolic-bulk criterion and the center-sign criterion are the same nonzero critical-displacement test.

**Theorem 1.10 (The unitary boundary is zero center curvature).**

$$\forall rho: \mathbb{C}, \operatorname{IsUnitary}(\operatorname{offlineZeroCharacter}(rho)) \iff \operatorname{normalizedCurvatureRayleighReadout}(\operatorname{criticalDisplacement}(rho), 0) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.offline_zero_character_unitary_iff_zero_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen unitary-axis criterion is exactly the zero set of the normalized center readout.

**Theorem 1.11 (Scale normalization gives the canonical polarity kernel).**

$$\forall delta: \mathbb{R}, \frac{delta^{2}}{2} \cdot \operatorname{normalizedCurvatureRayleighReadout}(delta, 0) = \operatorname{polarityKernelValue}(delta).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.normalized_center_readout_eq_polarity_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the center readout by delta squared over two yields zero on the unitary boundary and minus one in the hyperbolic bulk, exactly matching the selected one-point kernel.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.centerCurvaturePolarityKernel`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.detunedReflectedGenerator`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.evenChannelEnergyReadout`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.evenChannelNegativeSquareReadout`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.evenChannelState`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.normalizedCurvatureRayleighReadout`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.normalized_center_readout_eq_polarity_kernel`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.normalized_curvature_rayleigh_readout_formula`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.off_line_curvature_rayleigh_intertwiner`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.offline_zero_character_unitary_iff_zero_center`
- Truth anchor: `D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.offline_zero_monodromy_hyperbolic_iff_negative_center`
- Dependency: [D5/S3/Analytic/Adelic/OffLineCurvatureDipole](OffLineCurvatureDipole.md)
- Dependency: [D5/S3/Analytic/Adelic/ReflectedGrowthPairSecondOrderSpectrum](ReflectedGrowthPairSecondOrderSpectrum.md)
- Dependency: [D5/S3/Quantum/FiniteDimensional](../../Quantum/FiniteDimensional.md)
- Dependency: [D5/S3/Weil/Pick/HermitianKernelNegativeSquares](../../Weil/Pick/HermitianKernelNegativeSquares.md)
- Dependency: [D5/S3/Weil/ZetaLinear/OfflineZeroGeometricMonodromy](../../Weil/ZetaLinear/OfflineZeroGeometricMonodromy.md)
- Dependency: [D5/S3/Weil/ZetaLinear/Sylvester](../../Weil/ZetaLinear/Sylvester.md)
