# Dominance Event-Algebra Characterization

## Abstract

Complete dominance is exactly agreement on all observable events plus one separating event.

**Theorem 1.1 (Complete dominance has an event-algebra characterization).**

$$\forall X, O: Type, q: X \Rightarrow O,\\{}xAA, xAB, xBB: X, (\operatorname{ker}(q, xAA, xAB) \land \neg \operatorname{ker}(q, xAB, xBB)) \iff\\{}((\forall A\in \mathcal{P}(X), A\in \operatorname{observableEventAlgebra}(q) \Rightarrow \operatorname{indicator}(A, xAA) = \operatorname{indicator}(A, xAB)) \land\\{}\exists B\in \mathcal{P}(X), B\in \operatorname{observableEventAlgebra}(q) \land \operatorname{indicator}(B, xAB) \neq \operatorname{indicator}(B, xBB)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementAlgebra/DominanceEventAlgebraCharacterization.complete_dominance_event_algebra_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete dominance is the source kernel condition: the AA and AB states share one readout fiber, while AB and BB do not.

Every observable event therefore gives equal indicator values on AA and AB. Conversely, the readout fiber of AB supplies the observable event that distinguishes AB from BB.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementAlgebra/DominanceEventAlgebraCharacterization.complete_dominance_event_algebra_characterization`
- Dependency: [D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraDuality](ObservableEventAlgebraDuality.md)
