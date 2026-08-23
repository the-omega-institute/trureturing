# Process Concept Adjunction

## Abstract

Process pullback is left adjoint to the maximal predictable future concept.

**Theorem 1.1 (Process pullback is left adjoint to predictable future).**

$$\forall X \in Type, Y \in Type, p \in X \to Y, D \in \operatorname{ReadoutConcept}\left(Y\right), C \in \operatorname{ReadoutConcept}\left(X\right),\; \operatorname{pullbackConcept}\left(p, D\right) \le C \Leftrightarrow D \le \operatorname{pushforwardConcept}\left(p, C\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Adjunction/ProcessConceptAdjunction.process_concept_adjunction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any process, future readout D, and current readout C, the pullback of D refines C exactly when D refines the maximal future readout predictable from C.

The future readout is constructed by quotienting future states and current coordinates by the identifications generated along the process. A factor through the pullback descends to this quotient, and a factor from the quotient restricts back to current coordinates.

**Lemma 1.2 (The concept constructions form a Galois connection).**

$$\forall X \in Type, Y \in Type, p \in X \to Y,\; \operatorname{GaloisConnection}\left(pullbackConcept\left(p\right), pushforwardConcept\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Adjunction/ProcessConceptAdjunction.process_concept_galois_connection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointwise adjunction equivalence packages the process pullback and maximal predictable future operators as a Galois connection between the refinement preorders on future and current readout concepts.

**Lemma 1.3 (Process pullback preserves refinement).**

$$\forall X \in Type, Y \in Type, p \in X \to Y,\; \operatorname{Monotone}\left(pullbackConcept\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Adjunction/ProcessConceptAdjunction.pullback_concept_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If one future readout refines another, composing both readouts with the same process preserves that refinement. This monotonicity is the left-side order law supplied by the Galois connection.

**Lemma 1.4 (Predictable future preserves refinement).**

$$\forall X \in Type, Y \in Type, p \in X \to Y,\; \operatorname{Monotone}\left(pushforwardConcept\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Adjunction/ProcessConceptAdjunction.pushforward_concept_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Refining the current readout refines its maximal predictable future readout as well. This is the right-side monotonicity law obtained from the same Galois connection.

**Lemma 1.5 (The predictable future pulls back below the current concept).**

$$\forall X \in Type, Y \in Type, p \in X \to Y, C \in \operatorname{ReadoutConcept}\left(X\right),\; \operatorname{pullbackConcept}\left(p, \operatorname{pushforwardConcept}\left(p, C\right)\right) \le C$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Adjunction/ProcessConceptAdjunction.pullback_pushforward_refines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After constructing the maximal future readout predictable from a current concept and pulling it back along the process, the resulting current readout refines the original concept. This is the counit inequality of the adjunction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Adjunction/ProcessConceptAdjunction.process_concept_adjunction`
- Truth anchor: `D5/S3/ConceptDynamics/Adjunction/ProcessConceptAdjunction.process_concept_galois_connection`
- Truth anchor: `D5/S3/ConceptDynamics/Adjunction/ProcessConceptAdjunction.pullback_concept_monotone`
- Truth anchor: `D5/S3/ConceptDynamics/Adjunction/ProcessConceptAdjunction.pullback_pushforward_refines`
- Truth anchor: `D5/S3/ConceptDynamics/Adjunction/ProcessConceptAdjunction.pushforward_concept_monotone`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
