# Refinement and Observable Event Algebras

## Abstract

Realized-image refinement is dual to kernels and observable event algebras.

**Theorem 1.1 (Refinement, kernels, and event algebras are equivalent).**

$$\forall X, O, P: \operatorname{Type},\\{}q: X \to O, r: X \to P,\\{}(\operatorname{Refines}(\operatorname{rangeFactorization}(q), \operatorname{rangeFactorization}(r)) \iff \operatorname{ker}(r) \subseteq \operatorname{ker}(q)) \land\\{}(\operatorname{ker}(r) \subseteq \operatorname{ker}(q) \iff \operatorname{observableEventAlgebra}(q) \subseteq \operatorname{observableEventAlgebra}(r)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraDuality.observable_event_algebra_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An observable event is a subset of the state carrier whose membership is constant on every fiber of the readout. This is the source's event carrier, rather than a replacement by Boolean-valued maps.

Both readouts are normalized to their realized images before the factorization relation is tested. The existing effective-image criterion identifies that factorization with reverse inclusion of their equality kernels.

Reverse kernel inclusion transports every fiber-constant event from the coarser readout to the finer one. Conversely, the fiber containing one selected readout value is an observable event that separates any pair the coarser readout distinguishes.

Repository searches found no event-algebra definition on the exact set carrier. The adjacent Boolean-question algebra has a different carrier, while the imported kernel theorem supplies the first equivalence directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraDuality.observable_event_algebra_duality`
- Dependency: [D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality](../Refinement/ConceptKernelOrderDuality.md)
