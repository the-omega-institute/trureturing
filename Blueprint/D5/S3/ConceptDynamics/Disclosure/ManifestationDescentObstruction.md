# Manifestation Descent Obstruction

## Abstract

A distinction that becomes publicly visible after evolution cannot descend through a current public readout that identifies the two states.

**Theorem 1.1 (Manifestation obstructs noninterference descent).**

$$\begin{aligned}\forall X, L, Y, B: \operatorname{Type},\\l: X \to L, F: X \to Y,\\O: Y \to B, xAA, xAB: X,\\l\left(xAA\right) = l\left(xAB\right) \land O\left(F\left(xAA\right)\right) \neq O\left(F\left(xAB\right)\right) \Rightarrow\\\neg \operatorname{Refines}\left(O \circ F, l\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Disclosure/ManifestationDescentObstruction.manifestation_excludes_noninterference_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The future public readout is constructed by composing the evolution with the output interface. A descent through the current readout would preserve equality on every current-readout fiber.

The selected states occupy one such fiber but have different future outputs. Their manifestation therefore directly contradicts every candidate descent map.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Disclosure/ManifestationDescentObstruction.manifestation_excludes_noninterference_descent`
- Dependency: [D5/S3/ConceptDynamics/RefinementFactorization/RefinementShrinksIndistinguishability](../RefinementFactorization/RefinementShrinksIndistinguishability.md)
