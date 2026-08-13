# Independent Kill Rate

## Abstract

Independent coverage and visibility events give a product kill rate.

**Theorem 1.1 (Independent event rates multiply).**

$$\forall Outcome, \operatorname{MeasurableSpace}(Outcome), mu: \operatorname{Measure}(Outcome), C, V: \operatorname{Set}(Outcome), coverageRate, visibilityRate: \operatorname{ENNReal}, (\operatorname{IndepSet}(C, V, mu) \land mu(C) = coverageRate \land mu(V) = visibilityRate) \Rightarrow mu(\operatorname{inter}(C, V)) = coverageRate \times visibilityRate.$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/IndependentKillRate.independent_kill_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be the coverage event and V the visibility event in a measured outcome space. If the events are independent, and their measures are coverageRate and visibilityRate, then the measure of their intersection is the product of those two rates.

Pinned Mathlib was searched first for independent events and intersection measures. ProbabilityTheory.IndepSet.measure_inter_eq_mul was an exact hit, and ProbabilityTheory.indepSet_iff_measure_inter_eq_mul was a related hit. No existing D5 declaration stated this measure-theoretic event identity. The Lean theorem is a thin wrapper around the exact hit, followed only by rewriting the two named rates.

This is an honest partial closure of the source clause identifying killing with the intersection of independent coverage and visibility events. The finite parameter interpretation, regression interpretation, multi-site mutations, and biased behavior remain unresolved.

## References

- Truth anchor: `D5/S0/Naming/IndependentKillRate.independent_kill_rate`
