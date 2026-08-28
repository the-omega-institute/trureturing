# Canonical Completion Idempotence

## Abstract

Predictive completion is canonically idempotent.

**Definition 1.1 (The second completion is canonically equivalent to the first).**

$$\forall Y \in \operatorname{Type}, O \in \operatorname{Type}, update \in Y \to Y, readout \in Y \to O,\; \operatorname{Quotient}(\operatorname{secondStageRelation}(update, readout, id)) \equiv \operatorname{CompletedState}(update, readout).$$

*Formalization.* `D5/S3/ObserverMemory/Refinement/CanonicalCompletionIdempotence.canonical_completion_idempotence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A predictive completion is the quotient by equality of every future readout value, with its update and current readout induced from the source dynamics.

Completing that induced readout a second time produces the second-stage future relation. The existing cascade-completion construction supplies its canonical equivalence with the direct completion.

The Lean declaration exposes that equivalence itself, rather than only an inhabitation claim, by applying the repository's exact cascadeCompletionEquiv theorem with the identity forgetting map.

Repository search found the exact canonical declaration cascadeCompletionEquiv; it is imported and applied directly.

## References

- Truth anchor: `D5/S3/ObserverMemory/Refinement/CanonicalCompletionIdempotence.canonical_completion_idempotence`
- Dependency: [D5/S3/ObserverMemory/Refinement/CascadeCompletion](CascadeCompletion.md)
