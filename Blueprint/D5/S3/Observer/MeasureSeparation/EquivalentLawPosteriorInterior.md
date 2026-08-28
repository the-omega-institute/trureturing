# Posterior Interiority under Equivalent Laws

## Abstract

Equivalent transcript laws keep the limiting binary posterior strictly interior and exclude measurable zero-error separation.

**Theorem 1.1 (Equivalent laws keep the limiting posterior interior).**

$$\forall Omega: \operatorname{Type}, [\operatorname{MeasurableSpace}(Omega)],\\{}P_{x}, P_{y}: \operatorname{Measure}(Omega), a: \mathbb{R},\\{}\operatorname{ProbabilityMeasure}(P_{x}) \land \operatorname{ProbabilityMeasure}(P_{y}) \land\\{}0 < a \land a < 1 \land \operatorname{AbsolutelyContinuous}(P_{x}, P_{y}) \land \operatorname{AbsolutelyContinuous}(P_{y}, P_{x})\\{}\Rightarrow \operatorname{AlmostEverywhere}(\operatorname{ofReal}(a) P_{x} + \operatorname{ofReal}(1 - a) P_{y}, omega \mapsto 0 < \frac{a \operatorname{toReal}(\operatorname{rnDeriv}(P_{x}, P_{y}, omega))}{a \operatorname{toReal}(\operatorname{rnDeriv}(P_{x}, P_{y}, omega)) + (1 - a)} \land \frac{a \operatorname{toReal}(\operatorname{rnDeriv}(P_{x}, P_{y}, omega))}{a \operatorname{toReal}(\operatorname{rnDeriv}(P_{x}, P_{y}, omega)) + (1 - a)} < 1) \land\\{}\neg\exists A: \operatorname{Set}(Omega), \operatorname{Measurable}(A) \land P_{x}(A) = 1 \land P_{y}(A) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EquivalentLawPosteriorInterior.equivalent_law_posterior_stays_interior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two state-indexed transcript laws are probability measures on one measurable space. A real prior strictly between zero and one constructs their displayed mixture law.

The limiting likelihood is the real Radon--Nikodym density of the first law with respect to the second. Mutual absolute continuity makes this density finite and positive almost everywhere under the mixture, so the displayed Bayesian normalization is strictly between zero and one.

The second conjunct applies the frozen null-set transport result: no measurable event can have mass one under the first law and mass zero under the equivalent second law.

## References

- Truth anchor: `D5/S3/Observer/MeasureSeparation/EquivalentLawPosteriorInterior.equivalent_law_posterior_stays_interior`
- Dependency: [D5/S3/Observer/MeasureSeparation/EquivalentMeasuresExcludePerfectSeparator](EquivalentMeasuresExcludePerfectSeparator.md)
