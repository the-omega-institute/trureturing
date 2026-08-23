# Symmetric Events Have No Unique Culprit

## Abstract

A completely symmetric event cannot have an equivariant unique culprit when at least two subject labels are available.

**Theorem 1.1 (A symmetric event has no equivariant unique culprit).**

$$\begin{gathered}\forall n: \mathbb{N}, Event: \operatorname{Type},\\{}act: \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right) \to Event \to Event,\\{}culprit: Event \to \operatorname{Fin}\left(n\right), event: Event,\\{}(2 \leq n \land \operatorname{IsEquivariantCulprit}\left(act, culprit\right) \land \operatorname{IsCompletelySymmetric}\left(act, event\right)) \Rightarrow False.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/SymmetricEventNoUniqueCulprit.symmetric_event_admits_no_equivariant_culprit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose at least two subject labels are available, every relabeling fixes the event, and the culprit selector commutes with every relabeling. Choose a label distinct from the selected culprit and swap the two labels.

Complete symmetry leaves the event unchanged, so the selector must retain its value. Equivariance simultaneously requires the swap to move that value to the distinct label, which is impossible.

**Lemma 1.2 (The one-point event is completely symmetric).**

$$\forall n: \mathbb{N}, \operatorname{IsCompletelySymmetric}\left(\operatorname{trivialEventAction}\left(n\right), ()\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/SymmetricEventNoUniqueCulprit.trivial_event_is_completely_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-point event space supplies a concrete symmetric event for every number of subject labels. Its action always returns the sole event, so every permutation fixes that event and the symmetry premise is not vacuous.

**Lemma 1.3 (An anchored event admits an equivariant culprit).**

$$\forall n: \mathbb{N}, \exists culprit: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right), \operatorname{IsEquivariantCulprit}\left(anchoredEventAction, culprit\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/SymmetricEventNoUniqueCulprit.anchored_event_admits_equivariant_culprit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When an event carries a subject label that is transported by relabeling, the identity map selects that transported label equivariantly. Thus equivariance alone does not prevent a unique culprit; the obstruction comes from complete symmetry of the event.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/SymmetricEventNoUniqueCulprit.anchored_event_admits_equivariant_culprit`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/SymmetricEventNoUniqueCulprit.symmetric_event_admits_no_equivariant_culprit`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/SymmetricEventNoUniqueCulprit.trivial_event_is_completely_symmetric`
