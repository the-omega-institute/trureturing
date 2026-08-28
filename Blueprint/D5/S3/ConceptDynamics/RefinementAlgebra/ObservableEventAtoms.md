# Atoms of a Finite Observable-Event Algebra

## Abstract

The nonempty atoms of a finite observable-event algebra are exactly its effective fibers.

**Theorem 1.1 (Nonzero observable atoms are the realized readout fibers).**

$$\forall X \in \operatorname{Type}, O \in \operatorname{Type}, q \in X \to O, A \in \operatorname{Set}\left(X\right),\; \operatorname{Finite}\left(X\right) \Rightarrow (\operatorname{Nonempty}\left(A\right) \land \left(A \in \operatorname{observableEventAlgebra}\left(q\right) \land \left(\forall B \in \operatorname{Set}\left(X\right),\; \left(\operatorname{Nonempty}\left(B\right) \land \left(B \in \operatorname{observableEventAlgebra}\left(q\right) \land B \subseteq A\right)\right) \Rightarrow A \subseteq B\right)\right)) \iff \exists o\in \operatorname{range}\left(q\right), A = \left\{q\left(x\right) = o \mid x \in X\right\}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAtoms.nonzero_observable_atoms_are_effective_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be finite and let q be a readout. An observable event is a subset whose membership is constant on each q-fiber, using the existing observable-event algebra on the exact set carrier.

A nonempty event is an atom when every nonempty observable subevent contained in it contains it in return. Such an event is exactly the fiber over one value in the realized range of q.

The forward direction chooses a state in the event and compares it with that state's observable fiber. The reverse direction chooses a representative of the realized value and uses fiber constancy to show that every nonempty observable subevent contains the fiber.

Pinned Mathlib atom lemmas concern the full powerset lattice. Repository and library searches found no theorem for this observable subalgebra.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAtoms.nonzero_observable_atoms_are_effective_fibers`
- Dependency: [D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraDuality](ObservableEventAlgebraDuality.md)
