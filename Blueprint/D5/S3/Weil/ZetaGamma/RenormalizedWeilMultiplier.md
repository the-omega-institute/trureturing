# Renormalized Weil Multiplier

## Abstract

The classical zero-side Weil form is the Fourier multiplier form obtained by subtracting the finite prime-continuum discrepancy from the shifted Archimedean baseline.

**Theorem 1.1 (The completed Weil form is a single discrepancy multiplier).**

$$\begin{aligned}\forall Z: \operatorname{ZeroData}, f\in \mathcal{W}, L\in \mathbb{R},\\hL: 0 < L, hSupport: \operatorname{tsupport}\left(f\right) \subseteq [-L, L],\\hZero: \operatorname{SymmetricConvergent}\left(Z, \operatorname{convolutionSquare}\left(f\right)\right), hArch: \operatorname{ArchimedeanConvergent}\left(\operatorname{convolutionSquare}\left(f\right)\right) \Rightarrow\\\operatorname{let} b_{\infty}(\xi) = \Re(\psi(\frac{1}{4} + \frac{i \xi}{2})) - \operatorname{log}\left(\pi\right) + \frac{1}{\xi^{2} + \frac{1}{4}},\\r_{L}(\xi) = -2\pi \operatorname{PX}\left(\operatorname{exp}\left(2L\right), \xi\right) - \int_{\mathbb{R}} \operatorname{EL}\left(2L, u\right) \Re(\operatorname{exp}\left(-i \xi u\right)) du,\\\operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(f\right), hZero\right) = \frac{1}{2\pi} \int_{\mathbb{R}} (b_{\infty}(\xi) - r_{L}(\xi)) \lvert\operatorname{fourierLaplace}\left(f, \xi\right)\rvert^{2} d\xi.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/RenormalizedWeilMultiplier.renormalized_weil_multiplier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

W is the canonical carrier of even smooth compactly supported complex tests. The positive scale and support premise place the convolution square in the explicit-formula window, while hZero and hArch supply its two convergence witnesses.

The displayed b-infinity is constructed from the unshifted digamma and the Green resolvent term; r-L uses the canonical finite prime multiplier PX and continuous reference density EL. The digamma recurrence identifies this baseline with the shifted chart and yields the single multiplier.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/RenormalizedWeilMultiplier.renormalized_weil_multiplier`
- Dependency: [D5/S3/Weil/ZetaBridge/FixedScaleWeilQuadraticForm](../ZetaBridge/FixedScaleWeilQuadraticForm.md)
- Dependency: [D5/S3/Weil/ZetaGamma/PoleContinuumCompletion](PoleContinuumCompletion.md)
