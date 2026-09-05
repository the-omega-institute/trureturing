# Indexed Observation Closure Laws

## Abstract

An arbitrary indexed universe of heterogeneous observations induces an extensive, monotone, idempotent closure with redundant added members.

**Theorem 1.1 (Heterogeneous indexed observations generate a Galois closure).**

$$\forall I \in Type, X \in Type, Y \in I \to Type, q \in \left(\forall i \in I,\; X \to Y\left(i\right)\right), Q \in \operatorname{Set}\left(I\right), Q2 \in \operatorname{Set}\left(I\right),\; \operatorname{indexedObservationClosure}\left(q, Q\right) = \operatorname{invariantObservationIndices}\left(q, \operatorname{selectedObservationKernel}\left(q, Q\right)\right) \land \left(Q \subseteq \operatorname{indexedObservationClosure}\left(q, Q\right) \land \left(\left(Q \subseteq Q2 \Rightarrow \operatorname{indexedObservationClosure}\left(q, Q\right) \subseteq \operatorname{indexedObservationClosure}\left(q, Q2\right)\right) \land \left(\operatorname{indexedObservationClosure}\left(q, \operatorname{indexedObservationClosure}\left(q, Q\right)\right) = \operatorname{indexedObservationClosure}\left(q, Q\right) \land \left(\forall i \in I,\; i \in \operatorname{indexedObservationClosure}\left(q, Q\right) \Rightarrow \operatorname{selectedObservationKernel}\left(q, \operatorname{insert}\left(i, Q\right)\right) = \operatorname{selectedObservationKernel}\left(q, Q\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Closure/IndexedObservationClosureLaws.indexed_observation_closure_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observation universe is an arbitrary index type. Each index may have its own output type, so the statement does not collapse the source language to one shared codomain or to all functions into it.

The selected kernel K records pairs identified by every chosen index, and I returns exactly the indices whose observations are invariant on a relation. The first public clause exposes Cl(Q) = I(K(Q)).

The remaining public clauses state extensivity, monotonicity, idempotence, and the unchanged-kernel criterion for every observation admitted by the closure.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Closure/IndexedObservationClosureLaws.indexed_observation_closure_laws`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
