# Observable-Event Complement Persistence

## Abstract

Complementing an observable event preserves residual indistinguishability.

**Theorem 1.1 (Boolean negation cannot split a readout fiber).**

$$\forall X, O: \operatorname{Type},\\{}q: X \to O, A: \operatorname{Powerset}(X),\\{}x, y: X,\\{}A\in \operatorname{observableEventAlgebra}(q) \land \operatorname{ker}(q, x, y) \Rightarrow\\{}A^{{c}}\in \operatorname{observableEventAlgebra}(q) \land\\{}(x\in A \iff y\in A) \land\\{}(x\in A^{{c}} \iff y\in A^{{c}}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventComplementPersistence.observable_event_complement_persistence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An observable event has constant membership on every fiber of the readout. Negating that membership preserves the same equivalence.

The displayed conclusion records complement closure together with the membership equivalences for the event and its complement.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventComplementPersistence.observable_event_complement_persistence`
- Dependency: [D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraDuality](ObservableEventAlgebraDuality.md)
