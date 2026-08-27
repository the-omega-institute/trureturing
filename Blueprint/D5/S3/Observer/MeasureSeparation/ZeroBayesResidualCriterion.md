# Zero Bayes Residual Criterion

## Abstract

Equal-prior statistical residual vanishes exactly when the transcript laws are mutually singular.

**Definition 1.1 (Statistical residual is half the common mass).**

$$\forall Omega: \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(Omega\right)],\\{}P_{x}, P_{y}: \operatorname{Measure}\left(Omega\right),\\{}\operatorname{statisticalResidual}\left(P_{x}, P_{y}\right) = \frac{\operatorname{measureReal}\left(\operatorname{measureInf}\left(P_{x}, P_{y}\right), univ\right)}{2}.$$

*Formalization.* `D5/S3/Observer/MeasureSeparation/ZeroBayesResidualCriterion.statisticalResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The infimum of two measures is their canonical common mass. For two probability laws, half of its mass on the full transcript space is the equal-prior optimal binary error, equivalently the Le Cam one-minus-total-variation formula.

**Theorem 1.2 (Zero residual is equivalent to mutual singularity).**

$$\forall Omega: \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(Omega\right)],\\{}P_{x}, P_{y}: \operatorname{Measure}\left(Omega\right),\\{}\operatorname{ProbabilityMeasure}\left(P_{x}\right) \land \operatorname{ProbabilityMeasure}\left(P_{y}\right) \Rightarrow \operatorname{statisticalResidual}\left(P_{x}, P_{y}\right) = 0 \Leftrightarrow \operatorname{MutuallySingular}\left(P_{x}, P_{y}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MeasureSeparation/ZeroBayesResidualCriterion.statistical_residual_eq_zero_iff_mutually_singular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transcript carrier is arbitrary and both state-indexed laws are probability measures on its measurable structure.

Zero residual is zero total common mass. That is exactly a zero measure infimum, hence lattice disjointness; the pinned Mathlib equivalence identifies disjoint measures with mutually singular measures.

## References

- Truth anchor: `D5/S3/Observer/MeasureSeparation/ZeroBayesResidualCriterion.statisticalResidual`
- Truth anchor: `D5/S3/Observer/MeasureSeparation/ZeroBayesResidualCriterion.statistical_residual_eq_zero_iff_mutually_singular`
