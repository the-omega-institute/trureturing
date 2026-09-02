# White Spectrum Delta Normalization

## Abstract

Angular-frequency normalization turns white Lebesgue spectrum into ordinary Lebesgue measure, whose inverse Fourier transform is the Dirac distribution.

**Definition 1.1 (Angular frequency pushforward).**

$$\forall \nu \in \operatorname{Measure}(\mathbb{R}), \operatorname{angularFrequencyPushforward}(\nu) = \operatorname{map}(mathlibFrequency, \nu).$$

*Formalization.* `D5/S3/Weil/TestFunctions/WhiteSpectrumDeltaNormalization.angularFrequencyPushforward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate xi divided by two pi converts the repository's angular frequency to Mathlib's standard Fourier frequency.

**Proposition 1.2 (Normalized white spectrum becomes Lebesgue measure).**

$$\operatorname{angularFrequencyPushforward}(m_{0}) = \operatorname{volume}(\mathbb{R}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/WhiteSpectrumDeltaNormalization.normalized_white_frequency_pushforward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Jacobian of xi mapped to xi divided by two pi cancels the source density one over two pi exactly.

**Definition 1.3 (Inverse angular Fourier transform).**

$$\forall \nu \in \operatorname{Measure}(\mathbb{R}), \operatorname{inverseAngularFourier}(\nu) = \operatorname{fourierInv}(\operatorname{toTemperedDistribution}(\operatorname{angularFrequencyPushforward}(\nu))).$$

*Formalization.* `D5/S3/Weil/TestFunctions/WhiteSpectrumDeltaNormalization.inverseAngularFourier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a measure whose pushed-forward form has temperate growth, the angular inverse transform is Mathlib's distributional inverse Fourier transform after the frequency-coordinate change.

**Theorem 1.4 (Normalized white spectrum transforms to Dirac mass).**

$$\operatorname{inverseAngularFourier}(m_{0}) = \delta_{0}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/WhiteSpectrumDeltaNormalization.normalized_white_spectrum_inverse_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized angular white spectrum pushes forward to ordinary Lebesgue measure. Mathlib's tempered-distribution Fourier pair then identifies its inverse transform with delta at zero.

No Weil source, local completion, resolvent estimate, or Riemann hypothesis input is used in this normalization identity.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/WhiteSpectrumDeltaNormalization.angularFrequencyPushforward`
- Truth anchor: `D5/S3/Weil/TestFunctions/WhiteSpectrumDeltaNormalization.inverseAngularFourier`
- Truth anchor: `D5/S3/Weil/TestFunctions/WhiteSpectrumDeltaNormalization.normalized_white_frequency_pushforward`
- Truth anchor: `D5/S3/Weil/TestFunctions/WhiteSpectrumDeltaNormalization.normalized_white_spectrum_inverse_fourier`
- Dependency: [D5/S3/Weil/TestFunctions/WhiteToHaarIdentity](WhiteToHaarIdentity.md)
