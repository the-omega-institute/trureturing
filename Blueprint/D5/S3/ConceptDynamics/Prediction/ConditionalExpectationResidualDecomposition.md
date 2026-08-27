# Conditional Expectation Residual Decomposition

## Abstract

Conditional expectation gives the canonical orthogonal residual decomposition over a concept-generated sigma-algebra.

**Theorem 1.1 (Conditional expectation residuals are orthogonal).**

$$\begin{gathered}\forall X, B: \operatorname{Type},\\{}SigmaX: \operatorname{MeasurableSpace}\left(X\right), SigmaB: \operatorname{MeasurableSpace}\left(B\right),\\{}mu: \operatorname{Measure}\left(X\right), C: X \to B,\\{}T: \operatorname{L2}\left(X, mu, \mathbb{R}\right), \operatorname{Measurable}\left(C, SigmaX, SigmaB\right)\\{}\Rightarrow \exists! R: \operatorname{L2}\left(X, mu, \mathbb{R}\right),\\{}R = T - \operatorname{condExpL2}\left(T, \operatorname{comap}\left(C, SigmaB\right), SigmaX, mu\right) \land T = \operatorname{condExpL2}\left(T, \operatorname{comap}\left(C, SigmaB\right), SigmaX, mu\right) + R \land\\{}\forall Z: \operatorname{lpMeas}\left(\mathbb{R}, 2, \operatorname{comap}\left(C, SigmaB\right), SigmaX, mu\right), \operatorname{inner}\left(R, Z\right) = 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Prediction/ConditionalExpectationResidualDecomposition.conditional_expectation_residual_orthogonal_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ambient and concept-value measurable spaces are explicit. The concept map constructs its generated sigma-algebra by measurable-space comap, and the estimate is Mathlib's real L2 conditional expectation on that subspace.

The unique residual is publicly identified as the target minus that estimate, reconstructs the target, and has zero inner product with every square-integrable variable in the same generated measurable subspace.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Prediction/ConditionalExpectationResidualDecomposition.conditional_expectation_residual_orthogonal_decomposition`
- Dependency: [D5/S3/ConceptDynamics/Prediction/ConditionalExpectationOptimality](ConditionalExpectationOptimality.md)
