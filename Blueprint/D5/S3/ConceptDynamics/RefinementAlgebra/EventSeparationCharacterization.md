# Event Separation Characterization

## Abstract

Readout-equivalent states are exactly those agreeing on every observable event.

**Theorem 1.1 (Observable events separate distinct readout fibers).**

$$\forall X, O: Type, q: X \Rightarrow O, x, y: X,\\{}\operatorname{ker}(q, x, y) \iff \forall A\in \mathcal{P}(X), A\in \operatorname{observableEventAlgebra}(q) \Rightarrow (x\in A \iff y\in A).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementAlgebra/EventSeparationCharacterization.event_separation_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fiber-constant membership gives the forward implication. For the reverse implication, the observable fiber through the first state separates any state with a different readout.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementAlgebra/EventSeparationCharacterization.event_separation_characterization`
- Dependency: [D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraDuality](ObservableEventAlgebraDuality.md)
