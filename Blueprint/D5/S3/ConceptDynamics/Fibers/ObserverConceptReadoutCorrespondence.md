# Observer and Concept Readout Correspondence

## Abstract

Concepts embed as singleton observers and observer identity descends to a quotient.

**Theorem 1.1 (Embedding, forgetting, and relative identity).**

$$\begin{gathered}\forall X, C, I: \operatorname{Type},\\{}B: I \to \operatorname{Type}, q: X \to C, a: X,\\{}O: \operatorname{ObserverStructure}\left(X, I, B\right),\\{}E := \operatorname{conceptObserver}\left(q, a\right),\\{}J := \operatorname{jointReadout}\left(\operatorname{readout}\left(O\right)\right), p := \operatorname{quotientClassMap}\left(J\right),\\{}[(\operatorname{readout}\left(E\right)\left(unit\right) = q \land \left(\operatorname{admissible}\left(E\right) = {\Lambda k, True} \land \operatorname{anchor}\left(E\right) = a\right)) \land\\{}(\forall x \in X, y \in X,\; \operatorname{jointReadout}\left(\operatorname{readout}\left(E\right)\right)\left(x\right) = \operatorname{jointReadout}\left(\operatorname{readout}\left(E\right)\right)\left(y\right) \Leftrightarrow q\left(x\right) = q\left(y\right)) \land\\{}(\forall x \in X, y \in X,\; p\left(x\right) = p\left(y\right) \Leftrightarrow \operatorname{jointReadout}\left(\operatorname{readout}\left(O\right)\right)\left(x\right) = \operatorname{jointReadout}\left(\operatorname{readout}\left(O\right)\right)\left(y\right)) \land\\{}(\exists O1, O2: \operatorname{ObserverStructure}\left(Bool, Unit, {\Lambda k, Bool}\right), \operatorname{admissible}\left(O1\right) \ne \operatorname{admissible}\left(O2\right) \land \operatorname{ker}\left(\operatorname{jointReadout}\left(\operatorname{readout}\left(O1\right)\right)\right) = \operatorname{ker}\left(\operatorname{jointReadout}\left(\operatorname{readout}\left(O2\right)\right)\right)) \land\\{}(\exists O1, O2: \operatorname{ObserverStructure}\left(Bool, Unit, {\Lambda k, Unit}\right), \operatorname{anchor}\left(O1\right) \ne \operatorname{anchor}\left(O2\right) \land \operatorname{ker}\left(\operatorname{jointReadout}\left(\operatorname{readout}\left(O1\right)\right)\right) = \operatorname{ker}\left(\operatorname{jointReadout}\left(\operatorname{readout}\left(O2\right)\right)\right)) \land\\{}(\exists r, s: Bool \to \left(Bool \to Bool\right), r \ne s \land \operatorname{ker}\left(\operatorname{jointReadout}\left(r\right)\right) = \operatorname{ker}\left(\operatorname{jointReadout}\left(s\right)\right))].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/ObserverConceptReadoutCorrespondence.observer_concept_readout_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The singleton observer is public through its computation rules: its sole readout is the supplied concept, its admission predicate is universally true, and its anchor is the supplied state.

For an arbitrary dependent readout family, forgetting forms the canonical quotient projection by the kernel of the joint readout. Equality in that quotient is exactly observer-relative identity.

Three explicit Boolean countermodels show that equal readout kernels do not retain admission, anchor, or the coordinate decomposition of the joint readout.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Fibers/ObserverConceptReadoutCorrespondence.observer_concept_readout_correspondence`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
