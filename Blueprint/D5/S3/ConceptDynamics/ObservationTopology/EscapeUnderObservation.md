# Escape Under Observation

## Abstract

Injective observation preserves escapes; noninjective hides one on inhabited input.

**Theorem 1.1 (Injective observation preserves every displayed catalog escape).**

$$\begin{gathered}\forall observe: Output \to Observation, catalog: Index \to Input \to Output,\\{}candidate: Input \to Output, (\operatorname{Injective}\left(observe\right) \land \operatorname{CatalogEscape}\left(catalog, candidate\right)) \Rightarrow\\{}\operatorname{CatalogEscape}\left(\operatorname{observedCatalog}\left(observe, catalog\right), \operatorname{observedCandidate}\left(observe, candidate\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/EscapeUnderObservation.injective_preserves_catalog_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Postcomposition applies the same observation to every catalog row and to the candidate.

If an observed candidate agreed with an observed row, injectivity would recover pointwise agreement before observation.

That recovered equality contradicts the supplied CatalogEscape. The conclusion therefore retains both the injectivity and original-escape hypotheses.

**Theorem 1.2 (Every noninjective observation hides a one-row escape).**

$$\begin{gathered}\forall observe: Output \to Observation,\\{}(\operatorname{Nonempty}\left(Input\right) \land \neg \operatorname{Injective}\left(observe\right)) \Rightarrow\\{}(\exists catalog: Unit \to Input \to Output, \exists candidate: Input \to Output, (\operatorname{CatalogEscape}\left(catalog, candidate\right) \land \operatorname{Mem}\left(\operatorname{observedCandidate}\left(observe, candidate\right), \operatorname{range}\left(\operatorname{observedCatalog}\left(observe, catalog\right)\right)\right))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/EscapeUnderObservation.noninjective_hides_some_catalog_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the input carrier is inhabited and the observation is not injective. Choose distinct outputs with the same observation.

A constant one-row catalog at the first output omits the constant candidate at the second output; inhabitedness detects their difference.

After observation the two constant functions agree, so the genuine escape lies in the observed catalog range. The theorem asserts existence of this catalog and candidate, not that every escape is hidden.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/EscapeUnderObservation.injective_preserves_catalog_escape`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/EscapeUnderObservation.noninjective_hides_some_catalog_escape`
- Dependency: [D5/S0/Diagonal/Lawvere/QualitativeEscape](../../../S0/Diagonal/Lawvere/QualitativeEscape.md)
