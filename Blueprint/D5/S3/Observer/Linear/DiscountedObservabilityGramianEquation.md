# Discounted Observability Gramian Equation

## Abstract

The discounted observability Gramian satisfies its Lyapunov equation.

**Theorem 1.1 (The discounted Gramian obeys the fixed-point equation).**

$$\begin{gathered}\forall K, V, Y: \operatorname{Type}, \\{}[\operatorname{RCLike}(K)], [\operatorname{NormedAddCommGroup}(V)], [\operatorname{InnerProductSpace}(K, V)], [\operatorname{FiniteDimensional}(K, V)],\\{}[\operatorname{NormedAddCommGroup}(Y)], [\operatorname{InnerProductSpace}(K, Y)], [\operatorname{FiniteDimensional}(K, Y)],\\{}T: \operatorname{LinearMap}(K, V, V), C: \operatorname{LinearMap}(K, V, Y), \beta: \mathbb{R},\\{}0 < \beta < 1 \land \sqrt{\beta} \left\lVert T \right\rVert < 1 \Rightarrow\\{}\operatorname{discountedObservabilityGramian}(T, C, \beta) = C^{*} C + \beta T^{*} \operatorname{discountedObservabilityGramian}(T, C, \beta) T.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/DiscountedObservabilityGramianEquation.discounted_observability_gramian_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V and Y be finite-dimensional inner-product spaces over a real or complex scalar field. The evolution T and readout C are arbitrary linear maps on these carriers.

The discount beta lies strictly between zero and one, and the stated square-root norm bound makes the canonical discounted Gramian series summable.

Splitting off the zeroth Gram term gives the adjoint square of C. Every successor term is beta times the preceding term conjugated by T, so continuity transports the remaining infinite sum through that sandwich map.

Repository and pinned-library searches found no exact equation theorem. The proof directly applies the existing summability result, the zeroth-term sum split, adjoint reversal, and infinite-sum transport.

## References

- Truth anchor: `D5/S3/Observer/Linear/DiscountedObservabilityGramianEquation.discounted_observability_gramian_equation`
- Dependency: [D5/S3/Observer/Linear/DiscountedObservabilityGramianPositivity](DiscountedObservabilityGramianPositivity.md)
