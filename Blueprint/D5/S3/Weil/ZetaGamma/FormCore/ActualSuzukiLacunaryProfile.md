# Explicit lacunary Fourier profile

## Abstract

A concrete real centered-tent lacunary profile has infinite positive-log energy for its actual plus-sign unitary Fourier transform. The physical source and sharp sixth-moment construction consume this shared module.

**Definition 1.1 (Centered tent and lacunary cosine series).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiLacunaryProfile.counterProfile`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiLacunaryProfile.counterProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real profile is max(1-4*abs(t-1/2),0) times the cosine series with coefficients 2^(-(n+1)) and frequencies exp(4^(n+1)). Its continuity, support in [1/4,3/4] and value one at the center are proved from the explicit series.

**Definition 1.2 (Actual positive angular Fourier convention).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiLacunaryProfile.unitarySourceFourier`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiLacunaryProfile.unitarySourceFourier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual transform is (sqrt(2*pi))^(-1) times the mathlib Fourier transform at -xi/(2*pi). Equivalently its genuine L1 integral has kernel exp(i*xi*t) and unitary angular normalization.

**Theorem 1.3 (Actual positive-log Fourier energy is infinite).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiLacunaryProfile.actual_counterProfile_positive_log_top`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiLacunaryProfile.actual_counterProfile_positive_log_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The genuinely extended nonnegative integral of log-plus(abs(xi)) times the squared norm of the actual transform is infinity. An integrable coefficient-times-tent majorant justifies the series interchange. The tent transform is computed by interval-indicator convolution, including zero frequency.

The nonnegative two-channel spectral amplitude has density at least 1/(4096*pi) on pairwise disjoint bands of radius one around the lacunary frequencies. Each band has measure two. The source's Fourier identity is proved, not assumed. The support, center, integral-convention and divergence helpers are exported only for live downstream proofs; this split adds no mathematical claim.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiLacunaryProfile.actual_counterProfile_positive_log_top`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiLacunaryProfile.counterProfile`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiLacunaryProfile.unitarySourceFourier`
