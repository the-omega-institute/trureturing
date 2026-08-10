# Golden-Window Fourier Diffraction

## Abstract

The Fourier amplitude of a finite interval window is an exact sine kernel, specializing at golden-window length to the diffraction closed form.

**Theorem 1.1 (A finite interval window has exact sine-kernel amplitude).**

$$|\widehat c_{m}(\ell)|=\frac{|\sin(\pi m\ell)|}{\pi m},\quad m > 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/WindowDiffraction.window_fourier_amplitude` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive Fourier mode, integrating the complex exponential over the interval from zero to the window length and taking its norm gives the exact sine-kernel amplitude. The proof evaluates the exponential integral, reduces the complex norm to the sine half-angle identity, and uses positivity of the mode and pi to normalize the denominator.

**Theorem 1.2 (The golden window has the diffraction closed form).**

$$|\widehat c_{m}|=\frac{|\sin(\pi m/\varphi)|}{\pi m},\quad\varphi=\frac{1+\sqrt{5}}{2},\quad m > 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/WindowDiffraction.golden_window_fourier_amplitude` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cut-and-project interval window has length one over the golden ratio. Substituting this length into the general interval-window formula gives the exact diffraction amplitude |c-hat_m| = |sin(pi*m/phi)|/(pi*m), with no asymptotic approximation or omitted normalization factor.

## References

- Truth anchor: `D5/S3/Fourier/WindowDiffraction.golden_window_fourier_amplitude`
- Truth anchor: `D5/S3/Fourier/WindowDiffraction.window_fourier_amplitude`
