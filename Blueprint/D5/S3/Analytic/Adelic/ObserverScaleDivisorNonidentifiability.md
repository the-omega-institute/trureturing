# Observer Scale Divisor Nonidentifiability

## Abstract

Distinct positive observer parameters and distinct scale ratios can produce spectral zeta functions with the same zero-pole divisor.

**Theorem 1.1 (The spectral divisor does not determine observer scale).**

$$\exists P1 \in \operatorname{Ioi}(0, \mathbb{R}), c1 \in \operatorname{Ioi}(0, \mathbb{R}), P2 \in \operatorname{Ioi}(0, \mathbb{R}), c2 \in \operatorname{Ioi}(0, \mathbb{R}),\; P1 \ne P2 \land \left(c1 \ne c2 \land \left(\frac{P1}{c1} \ne \frac{P2}{c2} \land \left(\forall s \in \mathbb{C},\; \operatorname{meromorphicOrderAt}(\operatorname{observerSpectralZeta}(P1, c1), s) = \operatorname{meromorphicOrderAt}(riemannZeta, s) \land \operatorname{meromorphicOrderAt}(\operatorname{observerSpectralZeta}(P2, c2), s) = \operatorname{meromorphicOrderAt}(riemannZeta, s)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ObserverScaleDivisorNonidentifiability.observer_scale_not_recoverable_from_spectral_divisor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each observer reading is constructed from its positive circumference P, positive propagation coefficient c, and the Riemann zeta function.

The two witnesses have different P, different c, and different P over c. At every complex point, both readings have the same meromorphic order as the Riemann zeta function.

The proof applies the analytic nonzero-factor order theorem to the explicit exponential scale factor, so equality records zeros and poles with multiplicity rather than only equality of zero sets.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ObserverScaleDivisorNonidentifiability.observer_scale_not_recoverable_from_spectral_divisor`
