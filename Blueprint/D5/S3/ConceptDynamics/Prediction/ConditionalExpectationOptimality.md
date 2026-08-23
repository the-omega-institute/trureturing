# Conditional Expectation Optimality

## Abstract

Conditional expectation is the best squared-error predictor measurable through a concept.

**Theorem 1.1 (Conditional expectation minimizes mean-square error).**

$$\begin{gathered}\forall X, B: \operatorname{Type},\\{}mu: \operatorname{Measure}\left(X\right), C: X \to B,\\{}T: X \to \mathbb{R}, h: B \to \mathbb{R},\\{}\operatorname{Measurable}\left(C\right) \land \operatorname{MemLp}\left(T, 2, mu\right) \land\\{}\operatorname{Measurable}\left(h\right) \land \operatorname{MemLp}\left(h \circ C, 2, mu\right)\\{}\Rightarrow {\operatorname{L2Norm}\left(T - \operatorname{condExpL2}\left(T, \operatorname{comap}\left(C\right)\right), mu\right)}^{{2}} \leq {\operatorname{L2Norm}\left(T - h \circ C, mu\right)}^{{2}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Prediction/ConditionalExpectationOptimality.conditional_expectation_minimizes_mean_square_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concept map generates a sub-sigma-algebra by measurable-space comap. Every square-integrable measurable function of the concept belongs to the corresponding measurable subspace of the ambient real L2 space. Conditional expectation is its orthogonal projection, whose minimal-distance property gives the displayed squared-error bound.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Prediction/ConditionalExpectationOptimality.conditional_expectation_minimizes_mean_square_error`
