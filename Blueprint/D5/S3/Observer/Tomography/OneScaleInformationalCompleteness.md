# One-Scale Informational Completeness

## Abstract

All integer moments of one weighted Cayley pushforward determine the real spectrum.

**Theorem 1.1 (One complete Cayley scale determines the spectrum).**

$$\begin{gathered}\forall a: \mathbb{R},\\{}nu1, nu2: \operatorname{Measure}(\mathbb{R}),\\{}0 < a \land\\{}\operatorname{HasFiniteIntegral}(xi \mapsto \frac{1}{xi^{2} + a^{2}}, nu1) \land\\{}\operatorname{HasFiniteIntegral}(xi \mapsto \frac{1}{xi^{2} + a^{2}}, nu2) \Rightarrow\\{}\operatorname{let} density: \mathbb{R} \to \operatorname{ENNReal}() := xi \mapsto \operatorname{ofReal}(\frac{1}{xi^{2} + a^{2}}),\\{}\operatorname{let} cayleyPoint: \mathbb{R} \to Circle := xi \mapsto \operatorname{circlePoint}(\frac{xi + i\cdot a}{xi - i\cdot a}),\\{}\operatorname{let} cayleyCoordinate: \mathbb{R} \to \operatorname{AddCircle}(2 \cdot \pi) := xi \mapsto \operatorname{symm}(\operatorname{homeomorphCircle}', cayleyPoint\left(xi\right)),\\{}\operatorname{let} circleMeasure: \operatorname{Measure}(\mathbb{R}) \to \operatorname{Measure}(\operatorname{AddCircle}(2 \cdot \pi)) := nu \mapsto \operatorname{map}(cayleyCoordinate, \operatorname{withDensity}(nu, density)),\\{}(\forall n: \mathbb{Z}, \operatorname{integral}(circleMeasure\left(nu1\right), theta \mapsto fourier\left(n, theta\right)) = \operatorname{integral}(circleMeasure\left(nu2\right), theta \mapsto fourier\left(n, theta\right))) \Rightarrow nu1 = nu2.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/OneScaleInformationalCompleteness.one_scale_informational_completeness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proposition constructs the source resolvent density, the scaled Cayley point, its additive-circle coordinate, and the resulting pushforward measure from each real spectrum.

Finite resolvent budgets make both circle measures finite. Equality of every integer Fourier moment identifies them through the separating Fourier star algebra.

The Cayley coordinate is a measurable embedding. Pulling the measure equality back and cancelling the everywhere positive finite density recovers equality of the original real measures.

## References

- Truth anchor: `D5/S3/Observer/Tomography/OneScaleInformationalCompleteness.one_scale_informational_completeness`
