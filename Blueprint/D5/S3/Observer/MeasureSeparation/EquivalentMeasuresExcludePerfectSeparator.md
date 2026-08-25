# Equivalent Laws Exclude Perfect Separation

## Abstract

Equivalent probability laws admit no measurable event separating them with zero error.

**Theorem 1.1 (There is no zero-error separating event).**

$$\forall Omega: \operatorname{Type}, [\operatorname{MeasurableSpace}(Omega)],\\{}P_{x}, P_{y}: \operatorname{Measure}(Omega),\\{}\operatorname{ProbabilityMeasure}(P_{x}) \land \operatorname{ProbabilityMeasure}(P_{y}) \land \operatorname{AbsolutelyContinuous}(P_{x}, P_{y}) \land \operatorname{AbsolutelyContinuous}(P_{y}, P_{x})\\{}\Rightarrow \neg\exists A: \operatorname{Set}(Omega), \operatorname{Measurable}(A) \land P_{x}(A) = 1 \land P_{y}(A) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/EquivalentMeasuresExcludePerfectSeparator.equivalent_probability_laws_exclude_perfect_separator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two state-indexed transcript laws are probability measures on one measurable transcript space. Product equivalence is exposed as absolute continuity in both directions.

If the second law assigns a measurable event mass zero, absolute continuity forces the first law to assign it mass zero as well. It therefore cannot simultaneously have mass one under the first law.

The opposite singular regime is intentionally excluded: mutually singular laws can have measurable full-versus-null separating events.

Repository searches found no exact D5 theorem. The proof directly applies Mathlib's absolute-continuity null-set transport primitive.

## References

- Truth anchor: `D5/S3/Observer/MeasureSeparation/EquivalentMeasuresExcludePerfectSeparator.equivalent_probability_laws_exclude_perfect_separator`
