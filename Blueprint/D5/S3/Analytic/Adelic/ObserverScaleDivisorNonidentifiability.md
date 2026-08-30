# Observer Scale Divisor Nonidentifiability

## Abstract

Every positive observer pair has the same spectral zero-pole divisor; observers with both parameters distinct share it; and no function of that divisor can recover the observer's scale ratio.

**Theorem 1.1 (The spectral divisor does not determine observer scale).**

$$\left(\forall P1 \in \operatorname{Ioi}(0, \mathbb{R}), c1 \in \operatorname{Ioi}(0, \mathbb{R}), P2 \in \operatorname{Ioi}(0, \mathbb{R}), c2 \in \operatorname{Ioi}(0, \mathbb{R}), s \in \mathbb{C},\; \operatorname{meromorphicOrderAt}(\operatorname{observerSpectralZeta}(P1, c1), s) = \operatorname{meromorphicOrderAt}(\operatorname{observerSpectralZeta}(P2, c2), s)\right) \land \left(\left(\exists P1 \in \operatorname{Ioi}(0, \mathbb{R}), c1 \in \operatorname{Ioi}(0, \mathbb{R}), P2 \in \operatorname{Ioi}(0, \mathbb{R}), c2 \in \operatorname{Ioi}(0, \mathbb{R}),\; P1 \ne P2 \land \left(c1 \ne c2 \land \left(\forall s \in \mathbb{C},\; \operatorname{meromorphicOrderAt}(\operatorname{observerSpectralZeta}(P1, c1), s) = \operatorname{meromorphicOrderAt}(\operatorname{observerSpectralZeta}(P2, c2), s)\right)\right)\right) \land \left(\neg \left(\exists recover \in \left(\mathbb{C} \to \operatorname{WithTop}(\mathbb{Z})\right) \to \mathbb{R},\; \forall P \in \operatorname{Ioi}(0, \mathbb{R}), c \in \operatorname{Ioi}(0, \mathbb{R}),\; recover\left((s: \mathbb{C} \mapsto \operatorname{meromorphicOrderAt}(\operatorname{observerSpectralZeta}(P, c), s))\right) = \frac{P}{c}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ObserverScaleDivisorNonidentifiability.observer_scale_not_recoverable_from_spectral_divisor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each observer reading is constructed from its positive circumference P, positive propagation coefficient c, and the Riemann zeta function.

For every two positive observer pairs and every complex point, the two readings have equal meromorphic order. Thus all observers share the same divisor observation, not merely one selected pair.

The middle public conjunct exhibits two positive observers whose P values and c values are both unequal while their divisor observations agree at every complex point.

The final public conjunct rules out every function from a divisor reading to a real scale ratio that purports to recover P over c for all positive observers.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ObserverScaleDivisorNonidentifiability.observer_scale_not_recoverable_from_spectral_divisor`
