# Christoffel Support Decay

## Abstract

Unit-circle support supplies normalized monomial witnesses whose geometric energy bound forces exterior Christoffel costs to vanish.

**Theorem 1.1 (Unit-circle support forces exterior Christoffel decay).**

$$\forall mu \in \operatorname{Measure}\left(\operatorname{Complex}\left(\right)\right), w \in \operatorname{Complex}\left(\right),\; \left(\operatorname{IsFiniteMeasure}\left(mu\right) \land \left(1 < \left\lVert w \right\rVert \land \operatorname{Subset}\left(\operatorname{MeasureSupport}\left(mu\right), \operatorname{sphere}\left(0, 1\right)\right)\right)\right) \Rightarrow \left(\left(\forall N \in \operatorname{Nat}\left(\right),\; \operatorname{let} pN: \operatorname{Polynomial}\left(\operatorname{Complex}\left(\right)\right) := \operatorname{PolynomialMonomial}\left(N, \operatorname{pow}\left(\operatorname{inv}\left(w\right), N\right)\right); \operatorname{NatDegree}\left(pN\right) \le N \land \left(\operatorname{PolynomialEval}\left(pN, w\right) = 1 \land \left(\left(\forall z \in \operatorname{Complex}\left(\right),\; \operatorname{Mem}\left(z, \operatorname{sphere}\left(0, 1\right)\right) \Rightarrow \left\lVert \operatorname{PolynomialEval}\left(pN, z\right) \right\rVert = \operatorname{pow}\left(\operatorname{inv}\left(\left\lVert w \right\rVert\right), N\right)\right) \land \operatorname{ChristoffelEvaluationCost}\left(mu, w, N\right) \le \operatorname{MeasureOf}\left(mu, \operatorname{sphere}\left(0, 1\right)\right) \cdot \operatorname{pow}\left(\operatorname{inv}\left(\operatorname{ENNRealOfReal}\left(\left\lVert w \right\rVert\right)\right), 2 \cdot N\right)\right)\right)\right) \land \operatorname{Tendsto}\left((N \mapsto \operatorname{ChristoffelEvaluationCost}\left(mu, w, N\right)), atTop, \operatorname{nhds}\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/ChristoffelSupportDecay.christoffel_support_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every degree, the explicit polynomial w inverse to the N, times z to the N, has degree at most N, equals one at w, and has constant norm on the unit circle.

Support on that circle identifies its full energy with the circle mass times the squared geometric ratio. This admissible witness bounds the canonical cost, and the ratio is below one because w lies outside the circle.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/ChristoffelSupportDecay.christoffel_support_decay`
- Dependency: [D5/S3/Analytic/ZetaObservation/ChristoffelAtomFloor](ChristoffelAtomFloor.md)
