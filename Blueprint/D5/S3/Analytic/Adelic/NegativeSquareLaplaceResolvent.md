# Negative-Square Laplace Resolvent

## Abstract

A negative-square mode has an exact damping threshold and Laplace resolvent.

**Definition 1.1 (The stabilization gap).**

Lean statement: `D5/S3/Analytic/Adelic/NegativeSquareLaplaceResolvent.stabilizationGap`

*Formalization.* `D5/S3/Analytic/Adelic/NegativeSquareLaplaceResolvent.stabilizationGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The gap adds scalar damping to the frozen signed spectral atom. Because the atom is minus delta squared, the resulting denominator is damping minus delta squared.

**Definition 1.2 (The damped forward kernel).**

Lean statement: `D5/S3/Analytic/Adelic/NegativeSquareLaplaceResolvent.dampedNegativeSquareKernel`

*Formalization.* `D5/S3/Analytic/Adelic/NegativeSquareLaplaceResolvent.dampedNegativeSquareKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward kernel is the real exponential with rate equal to minus the stabilization gap. Its half-line integrability detects the exact damping threshold.

**Definition 1.3 (The scalar negative-square resolvent).**

Lean statement: `D5/S3/Analytic/Adelic/NegativeSquareLaplaceResolvent.negativeSquareResolvent`

*Formalization.* `D5/S3/Analytic/Adelic/NegativeSquareLaplaceResolvent.negativeSquareResolvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar resolvent is the inverse stabilization gap. Its pole occurs when the applied damping exactly equals the squared reflected split.

**Theorem 1.4 (Threshold, integrability, integral, and pole agree).**

$$\begin{aligned}\forall delta: \mathbb{R}, u: \mathbb{R}, {\operatorname{IntegrableOnIoi}(\operatorname{dampedNegativeSquareKernel}(delta, u), 0) \iff delta^{2} < u} \land\\{delta^{2} < u \Rightarrow \operatorname{IntegralIoi}(\operatorname{dampedNegativeSquareKernel}(delta, u), 0) = \operatorname{negativeSquareResolvent}(delta, u)} \land\\{0 < \operatorname{negativeSquareResolvent}(delta, u) \iff delta^{2} < u} \land\\{\operatorname{stabilizationGap}(delta, u) = 0 \iff u = delta^{2}}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/NegativeSquareLaplaceResolvent.negative_square_laplace_resolvent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pinned Mathlib improper-integral theorems show that the damped kernel is integrable on the positive half-line exactly when damping exceeds delta squared. Above this threshold, its integral is the inverse gap.

The same threshold characterizes positivity of the scalar resolvent, while equality marks its pole. This closes the local stabilization debt and does not construct a global zeta resolvent.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/NegativeSquareLaplaceResolvent.dampedNegativeSquareKernel`
- Truth anchor: `D5/S3/Analytic/Adelic/NegativeSquareLaplaceResolvent.negativeSquareResolvent`
- Truth anchor: `D5/S3/Analytic/Adelic/NegativeSquareLaplaceResolvent.negative_square_laplace_resolvent`
- Truth anchor: `D5/S3/Analytic/Adelic/NegativeSquareLaplaceResolvent.stabilizationGap`
- Dependency: [D5/S3/Analytic/Adelic/ReflectedGrowthPairSecondOrderSpectrum](ReflectedGrowthPairSecondOrderSpectrum.md)
