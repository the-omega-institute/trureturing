# The Dark-Side Receipt

## Abstract

Completing a countable metric space without isolated points makes the anonymous complement comeagre and measure one.

**Theorem 1.1 (Completion makes the anonymous complement comeagre and measure one).**

$$\operatorname{MetricSpace}(N), \operatorname{Countable}(N), \operatorname{PerfectSpace}(N), \neg\operatorname{CompleteSpace}(N),\\\operatorname{MeasurableSpace}(\operatorname{Completion}(N)), \operatorname{BorelSpace}(\operatorname{Completion}(N)), \mu : \operatorname{Measure}(\operatorname{Completion}(N)),\\\operatorname{NoAtoms}(\mu), \operatorname{IsProbabilityMeasure}(\mu) \Rightarrow\\\operatorname{DenseRange}(coe) \land \operatorname{PerfectSpace}(\operatorname{Completion}(N)) \land\\\operatorname{IsMeagre}(\operatorname{range}(coe)) \land \operatorname{complement}(\operatorname{range}(coe))\in \operatorname{residual}(\operatorname{Completion}(N)) \land\\\operatorname{Nonempty}(\operatorname{complement}(\operatorname{range}(coe))) \land \mu(\operatorname{complement}(\operatorname{range}(coe))) = 1$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/DarkSideReceipt.dark_side_receipt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N be a countable incomplete metric space without isolated points, let X be its metric completion, and let mu be any atomless Borel probability measure on X. The canonical embedding coe : N -> X has dense range by the defining property of completion. Density transfers the absence of isolated points from N to X.

Every singleton in the perfect metric space X is closed with empty interior, hence nowhere dense. The canonical image is countable, so it is meagre and its complement is residual (comeagre). Since X is complete metrizable, the Baire theorem makes that residual complement dense and therefore nonempty.

An atomless measure vanishes on the countable canonical image. Probability normalization then gives its complement measure one. The checked rational witness shows that all hypotheses are simultaneously realizable: Q is countable, perfect, and incomplete, while Lebesgue measure restricted to (0, 1] and transported across Completion(Q) ~= R is atomless and probabilistic.

## References

- Truth anchor: `D5/S0/Naming/DarkSideReceipt.dark_side_receipt`
