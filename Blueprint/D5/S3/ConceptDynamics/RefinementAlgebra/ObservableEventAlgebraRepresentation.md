# Observable-Event Algebra Representation

## Abstract

Fiber-constant events are canonically the powerset of the effective output.

**Theorem 1.1 (Observable events form the powerset of the realized range).**

$$\forall X, O: \operatorname{Type},\\{}q: X \to O,\\{}\exists! Phi: \operatorname{OrderIso}(\operatorname{observableEventBooleanAlgebra}(q), \operatorname{Powerset}(\operatorname{range}(q))),\\{}\forall A\in \operatorname{observableEventBooleanAlgebra}(q), Phi(A) = \operatorname{image}(\operatorname{rangeFactorization}(q), A).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraRepresentation.observable_event_algebra_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observable-event carrier is the existing predicate of subsets whose membership is constant on every readout fiber. It is bundled with the inherited union, intersection, complement, and empty event.

The canonical forward map sends an observable event to the realized readout values met by that event. The inverse pulls a set of realized values back along the range factorization.

Fiber constancy makes pullback after image recover the original event, while surjectivity onto the realized range makes image after pullback recover the original set of effective outputs.

The displayed computation rule uniquely determines the order isomorphism, and an order isomorphism between these Boolean algebras preserves all Boolean operations.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraRepresentation.observable_event_algebra_representation`
- Dependency: [D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraDuality](ObservableEventAlgebraDuality.md)
