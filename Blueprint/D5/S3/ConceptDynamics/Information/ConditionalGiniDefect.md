# Exact Conditional Gini Defect

## Abstract

The increase in conditional logical impurity equals a weighted squared posterior difference.

**Theorem 1.1 (Coarsening charges exactly the squared change of the posterior).**

$$\begin{gathered}\forall X, C, D, A: \operatorname{Type},\\{}p: \operatorname{PMF}(X), r: X \to D, t: X \to A, f: D \to C,\\{}\operatorname{I}(f \circ r) = \operatorname{I}(r) + \sum_{d} \sum_{a} \operatorname{M}(d) \cdot \operatorname{ofReal}((\operatorname{toReal}(\operatorname{P}(d, a)) - \operatorname{toReal}(\operatorname{Q}(\operatorname{f}(d), a)))^{2}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Information/ConditionalGiniDefect.conditional_gini_exact_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a probability mass function, r the refined readout, t the target, and f the coarsening map. I(s) denotes conditional logical impurity for readout s and the same p and t. M(d) is the refined fiber mass. P(d,a) and Q(f(d),a) are the refined and coarse joint target masses divided by their respective fiber masses. The ratios and sums use extended nonnegative reals. Each ratio is converted to a real before subtraction.

For one target value, the posterior ratio represents the conditional expectation of the target indicator almost everywhere. Nested conditional expectations split its squared prediction loss into the refined loss and the squared change of the two estimates. The sum of indicator losses equals ordered-pair impurity by the complementary collision identity. Summing the squared changes and grouping by refined fiber gives the displayed formula.

Zero-mass fibers contribute zero. The formula allows arbitrary carrier types and imposes no countability restriction on their ambient types. It concerns probability mass functions and deterministic readouts.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Information/ConditionalGiniDefect.conditional_gini_exact_defect`
- Dependency: [D5/S3/ConceptDynamics/Information/RefinementImpurityMonotonicity](RefinementImpurityMonotonicity.md)
- Dependency: [D5/S3/ConceptDynamics/Prediction/ConditionalExpectationRefinementPythagoras](../Prediction/ConditionalExpectationRefinementPythagoras.md)
