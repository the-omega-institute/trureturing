# Conditional Expectation Refinement Pythagoras

## Abstract

Nested conditioning sigma-algebras split squared prediction risk into later risk and conditional-expectation innovation.

**Theorem 1.1 (Refinement splits conditional-expectation risk).**

$$\begin{gathered}\forall X: \operatorname{Type},\\{}mu: \operatorname{Measure}\left(X\right),\\{}G_{q}, G_{r}, Sigma: \operatorname{MeasurableSpace}\left(X\right),\\{}T: \operatorname{L2}\left(X, mu, \mathbb{R}\right),\\{}G_{q} \subseteq G_{r} \land G_{r} \subseteq Sigma\\{}\Rightarrow ({\operatorname{L2Norm}\left(T - \operatorname{condExpL2}\left(T, G_{q}\right), mu\right)}^{{2}} = {\operatorname{L2Norm}\left(T - \operatorname{condExpL2}\left(T, G_{r}\right), mu\right)}^{{2}} + {\operatorname{L2Norm}\left(\operatorname{condExpL2}\left(T, G_{r}\right) - \operatorname{condExpL2}\left(T, G_{q}\right), mu\right)}^{{2}}) \land\\{}{\operatorname{L2Norm}\left(T - \operatorname{condExpL2}\left(T, G_{r}\right), mu\right)}^{{2}} \leq {\operatorname{L2Norm}\left(T - \operatorname{condExpL2}\left(T, G_{q}\right), mu\right)}^{{2}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Prediction/ConditionalExpectationRefinementPythagoras.conditional_expectation_refinement_pythagoras` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target is a real square-integrable random variable. The coarse and refined measurable spaces are both sub-sigma-algebras of the ambient space, with the coarse one contained in the refined one. The two displayed estimates are Mathlib's canonical L2 conditional expectations.

The refined-minus-coarse estimate is measurable for the refined sigma-algebra. It is therefore orthogonal to the residual after refined conditioning. Expanding that orthogonal sum gives the exact squared-norm identity; nonnegativity of the innovation term gives risk monotonicity.

For real L2 functions, squared L2 norm is the integral of the squared error, so the public norm identity is the canonical L2 carrier of the source's expected-square formula.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Prediction/ConditionalExpectationRefinementPythagoras.conditional_expectation_refinement_pythagoras`
- Dependency: [D5/S3/ConceptDynamics/Prediction/ConditionalExpectationOptimality](ConditionalExpectationOptimality.md)
