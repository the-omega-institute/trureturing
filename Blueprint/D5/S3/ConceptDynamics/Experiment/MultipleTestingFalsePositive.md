# False Positives under Multiple Testing

## Abstract

Independent repeated tests amplify false-positive risk, while every finite family obeys the union bound.

**Theorem 1.1 (At least one false positive).**

$$\begin{gathered}\forall Omega: \operatorname{Type}, mu: \operatorname{Measure}(Omega), k: \operatorname{Nat},\\{}alpha: \operatorname{Real}, E: \operatorname{Fin}(k) \to \operatorname{Set}(Omega),\\{}\operatorname{IsProbabilityMeasure}(mu) \land {\forall i: \operatorname{Fin}(k), \operatorname{Measurable}(\operatorname{event}(E, i)) \land \operatorname{Pr}(mu, \operatorname{event}(E, i)) = alpha} \land 0 \le alpha \land alpha \le 1 \Rightarrow \\{}{\operatorname{iIndepSet}(E, mu) \Rightarrow {\operatorname{Pr}(mu, \operatorname{iInterCompl}(E)) = {1 - alpha}^{k} \land \\{}\operatorname{Pr}(mu, \operatorname{iUnion}(E)) = 1 - {1 - alpha}^{k} \land \\{}{\forall m, n: \operatorname{Nat}, m \le n \Rightarrow 1 - {1 - alpha}^{m} \le 1 - {1 - alpha}^{n}} \land \\{}({2 \le k \land 0 < alpha \land alpha < 1} \Rightarrow alpha < \operatorname{Pr}(mu, \operatorname{iUnion}(E)))}} \land \\{}\operatorname{Pr}(mu, \operatorname{iUnion}(E)) \le k \times alpha.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/MultipleTestingFalsePositive.at_least_one_false_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outcome space, probability measure, finite family of measurable false-positive events, common single-test rate alpha, and number of tests k are public source primitives.

Under mutual independence, the no-error intersection has probability (1-alpha)^k and its complementary union has probability 1-(1-alpha)^k. The displayed family of search-wide rates is nondecreasing in k.

For k at least two and 0 < alpha < 1, the search-wide probability is strictly larger than alpha. This is the formal obstruction to reporting only the most successful test while retaining the single-test threshold as the whole-search error rate.

The final public conjunct does not assume independence: Mathlib's finite union bound gives probability at most k times alpha for every measurable family with the stated marginal rates.

Pinned Mathlib exact hits compute independent intersections, probability complements, finite union bounds, constant products, and power monotonicity. No repository theorem packages all five source clauses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/MultipleTestingFalsePositive.at_least_one_false_positive`
