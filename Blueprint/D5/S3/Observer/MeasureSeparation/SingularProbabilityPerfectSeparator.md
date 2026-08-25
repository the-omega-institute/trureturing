# Singular Probability Laws Have Perfect Separation

## Abstract

Mutually singular probability laws admit a measurable perfect separator.

**Theorem 1.1 (A measurable event separates singular laws with zero error).**

$$\forall Omega: \operatorname{Type}, [\operatorname{MeasurableSpace}(Omega)],\\{}P_{x}, P_{y}: \operatorname{Measure}(Omega),\\{}\operatorname{ProbabilityMeasure}(P_{x}) \land \operatorname{ProbabilityMeasure}(P_{y}) \land \operatorname{MutuallySingular}(P_{x}, P_{y})\\{}\Rightarrow \exists A_{x,y}: \operatorname{Set}(Omega), \operatorname{Measurable}(A_{x,y}) \land P_{x}(A_{x,y}) = 1 \land P_{y}(A_{x,y}) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/SingularProbabilityPerfectSeparator.mutually_singular_probability_laws_have_perfect_separator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two state-indexed transcript laws are probability measures on one measurable transcript space. Their mutual singularity is the product-singular premise established immediately before the source theorem.

Mathlib's canonical singular set is measurable, null under the first law, and has null complement under the second law. Its complement is therefore the required event.

The probability-measure instance turns nullity of the singular set into mass one for its complement. Thus the complete transcript distinguishes the two laws outside null sets.

Repository searches found only special or premise-heavier separation results. The proof applies the pinned measurable singular-set API directly.

## References

- Truth anchor: `D5/S3/Observer/MeasureSeparation/SingularProbabilityPerfectSeparator.mutually_singular_probability_laws_have_perfect_separator`
