# Golden Vertical Sampling

## Abstract

Fourier frequency on the golden scale circle equals vertical Mellin frequency on logarithmic scale.

**Theorem 1.1 (The Fundamental Golden Angular Frequency Is Positive).**

$$(0 < goldenAngularFrequency).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling.golden_angular_frequency_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fundamental frequency is pi divided by the positive logarithm of the golden ratio, so it is strictly positive.

This fixes the sign of the frequency normalization and does not assert an Euler-product identity.

**Theorem 1.2 (Golden Fourier Phase Equals Vertical Mellin Phase).**

$$\forall x: \mathbb{R}, k: \mathbb{Z},\\{}(2 \times \pi \times (k: \mathbb{R}) \times \operatorname{goldenScaleCoordinate}\left(x\right) = {(k: \mathbb{R}) \times goldenAngularFrequency} \times \operatorname{log}\left(x\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling.golden_phase_vertical_frequency_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real scale and integral mode, substituting the golden coordinate converts the Fourier phase into a logarithmic Mellin phase.

The equality is finite algebra using the chosen normalizations; no positivity or analytic convergence hypothesis is introduced.

**Theorem 1.3 (Adjacent Modes Have Fundamental Golden Spacing).**

$$\forall k: \mathbb{Z},\\{}({(k + 1: \mathbb{R}) \times goldenAngularFrequency} - {(k: \mathbb{R}) \times goldenAngularFrequency} = goldenAngularFrequency).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling.golden_vertical_mode_spacing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vertical frequencies attached to consecutive integral modes differ by exactly one fundamental frequency.

This is a spacing identity for the indexed frequencies and makes no claim about spectral values at those modes.

**Theorem 1.4 (The Zero Mode Has Zero Vertical Frequency).**

$$((0: \mathbb{R}) \times goldenAngularFrequency = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling.golden_vertical_zero_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the fundamental frequency by the real zero gives the uncharged scale-average frequency.

The statement identifies only the zero mode and does not characterize any nonzero Fourier coefficient.

## References

- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling.golden_angular_frequency_pos`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling.golden_phase_vertical_frequency_identity`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling.golden_vertical_mode_spacing`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling.golden_vertical_zero_mode`
- Dependency: [D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle](GoldenScaleCircle.md)
