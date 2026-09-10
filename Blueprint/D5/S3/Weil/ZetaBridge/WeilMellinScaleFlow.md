# Mellin Scale Flow

## Abstract

The original polynomial arithmetic Mellin window has an exact centered Fourier scale law; the same rescaled seed and all endpoint terms are retained.

**Definition 1.1 (The actual scaled seed in the existing window).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilMellinScaleFlow.scaledPolynomialWindow`

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilMellinScaleFlow.scaledPolynomialWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A polynomial H on the fixed interval gives h_a(t)=H(exp(-a)*t). Its coefficients are B_r*exp(-2r*a). Reuse polynomialMellinWindow and Zeta23.paperFT directly; do not introduce a second Fourier or model owner. The fixed polynomial is a certified approximation to varying prolate modes, not a renamed unknown ground state.

**Theorem 1.2 (Exact centered Fourier expression).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilMellinScaleFlow.scaled_polynomial_centered_paperFT`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilMellinScaleFlow.scaled_polynomial_centered_paperFT` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For included integers satisfying log(m)<=2a and Im(z)<1/2, multiply the actual Fourier integral by exp(-(1/2+i*z)*a). The upper-endpoint exponential becomes exp(-(2r+1/2+i*z)*log(m)); the lower term remains exp(-2*(2r+1/2+i*z)*a). Integrability and the original endpoint evaluation are inherited from the existing polynomial source, and the scaling cancellation is proved from exponential addition.

**Theorem 1.3 (Two actual scales with the same visible integer set).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilMellinScaleFlow.scaled_polynomial_paperFT_scale_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilMellinScaleFlow.scaled_polynomial_paperFT_scale_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtract the centered Fourier values at two scales. The upper endpoint cancels exactly, leaving the finite difference of the lower exponential terms. Neither a desired error bound nor a quadrature identity is a hypothesis. The paper scale-flow derivative follows from this formula; integer activation is joined where the new interval has zero length.

The new interval certificate independently encloses the true zeroth and fourth prolate modes for every a in log(3)/2 plus or minus 2e-8, including the entire Legendre complement. It controls varying seed error, actual moving arithmetic cutoffs, the nonzero origin denominator and the model-centered readout. The full operator realization and uniform transport bounds remain paper/computer-assisted bridges. No new same-scale Weil-ground readout bound, global rate or Xi limit is asserted. Lean elaboration, Scribe emission and transitive axiom checking have not run.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilMellinScaleFlow.scaledPolynomialWindow`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilMellinScaleFlow.scaled_polynomial_centered_paperFT`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilMellinScaleFlow.scaled_polynomial_paperFT_scale_difference`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow](WeilPolynomialMellinWindow.md)
