# Pole-Continuum Completion

## Abstract

The completed-zeta pole pair minus the continuous prime density is the decaying Green-kernel form, and its multiplier advances the digamma argument by one.

**Theorem 1.1 (The pole-continuum difference is the decaying Green form).**

$$\forall f\in \mathcal{W}, \operatorname{poleTerm}\left(\operatorname{convolutionSquare}\left(f\right)\right) - \int_{0}^{\infty} \operatorname{exp}\left(\frac{u}{2}\right) (\operatorname{convolutionSquare}\left(f, u\right) + \operatorname{convolutionSquare}\left(f, -u\right)) du = \int_{\mathbb{R}} \int_{\mathbb{R}} \operatorname{exp}\left(-\frac{\left|x-y\right|}{2}\right) \operatorname{f}\left(x\right) \overline{\operatorname{f}\left(y\right)} dy dx$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PoleContinuumCompletion.pole_continuum_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

W is the canonical carrier of even smooth compactly supported complex tests. The displayed half-line integral is the continuous prime main density evaluated on the canonical convolution square.

Splitting the two pole evaluations into growing and decaying exponentials cancels the growing half-line contribution. Fubini and translation invariance identify the remainder with the displayed full-line Green kernel.

**Theorem 1.2 (The Green multiplier advances the digamma argument by one).**

$$\begin{aligned}\forall xi\in \mathbb{R},\\\operatorname{let} b_{\infty} = \Re(\psi(\frac{1}{4} + \frac{i xi}{2})) - \operatorname{log}\left(\pi\right) + \frac{1}{xi^{2} + \frac{1}{4}},\\b_{\infty} = \Re(\psi(\frac{5}{4} + \frac{i xi}{2})) - \operatorname{log}\left(\pi\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PoleContinuumCompletion.archimedean_shift_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity is the exact digamma recurrence at one quarter plus half the imaginary frequency. Taking real parts turns the reciprocal term into the displayed Green multiplier.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/PoleContinuumCompletion.archimedean_shift_completion`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PoleContinuumCompletion.pole_continuum_completion`
