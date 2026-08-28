# Atoms of the Pullback Algebra

## Abstract

Minimal nonempty events in the canonical pullback algebra are realized fibers.

**Theorem 1.1 (Nonzero pullback atoms are exactly the realized fibers).**

$$\begin{gathered}\forall X, O: \operatorname{Type}, q: X \to O,\\{}\forall A: \operatorname{Set}(X),\\{}(\operatorname{Nonempty}(A) \land A \in \operatorname{PullbackAlgebra}(q) \land\\{}\forall C: \operatorname{Set}(X), \operatorname{Nonempty}(C) \land C \in \operatorname{PullbackAlgebra}(q) \land C \subseteq A \Rightarrow A \subseteq C) \iff\\{}(\exists o: \operatorname{range}(q), A = \{x: X \mid q(x) = \operatorname{val}(o)\}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementAlgebra/PullbackAlgebraFiberAtoms.nonzero_pullback_atoms_are_effective_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pullback algebra is the repository's canonical family of proposition-valued events that factor through the readout.

The left side states nonemptiness, pullback observability, and minimality against every nonempty observable subevent. The right side identifies the event with one fiber over a realized readout value.

A point in a nonempty minimal event selects its fiber. Fiber constancy puts that fiber inside the event, and minimality forces equality. Conversely, any nonempty observable subevent of a fiber contains the whole fiber.

No finiteness assumption is used: the characterization holds for arbitrary state and readout carriers, and therefore includes the finite-carrier corollary.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementAlgebra/PullbackAlgebraFiberAtoms.nonzero_pullback_atoms_are_effective_fibers`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
- Dependency: [D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence](../Dialectics/DeterministicInterfaceEquivalence.md)
