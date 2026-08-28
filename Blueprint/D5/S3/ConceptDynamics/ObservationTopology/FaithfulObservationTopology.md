# Faithful Observation Topology

## Abstract

Injective observations induce discrete topology and preserve catalog escapes.

**Theorem 1.1 (A readout induces the discrete topology exactly when it is injective).**

$$\forall observe: \operatorname{Concept}\left(X, Observation\right), \operatorname{partitionTopology}\left(observe\right) = \operatorname{bottomTopology}\left(X\right) \iff \operatorname{Injective}\left(observe\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/FaithfulObservationTopology.partitionTopology_eq_discrete_iff_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The partition topology identifies precisely those source points with equal observed values.

If the topology is discrete, inseparable source points are equal, so equal observations force equal inputs. Conversely, an injective readout has the same fibers as the identity.

The biconditional concerns equality with the bottom, hence discrete, topology on the source and adds no inhabitedness assumption.

**Theorem 1.2 (Discreteness is preservation of every one-row catalog escape).**

$$\begin{gathered}\forall observe: Output \to Observation,\\{}([\operatorname{Nonempty}\left(Input\right)]) \Rightarrow\\{}(\operatorname{partitionTopology}\left(observe\right) = \operatorname{bottomTopology}\left(Output\right) \iff (\forall catalog: Unit \to Input \to Output, candidate: Input \to Output,\\{}\operatorname{CatalogEscape}\left(catalog, candidate\right) \Rightarrow\\{}\operatorname{CatalogEscape}\left(\operatorname{observedCatalog}\left(observe, catalog\right), \operatorname{observedCandidate}\left(observe, candidate\right)\right))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/FaithfulObservationTopology.discrete_partition_iff_preserves_unit_catalog_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the catalog input type is inhabited. The theorem compares discreteness of the observation partition with a universal one-row escape-preservation law.

For every Unit-indexed catalog and candidate, a genuine escape before observation must remain an escape after both are postcomposed with the observation.

The statement is an exact biconditional. It does not assert the preservation law without the displayed Nonempty instance.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/FaithfulObservationTopology.discrete_partition_iff_preserves_unit_catalog_escape`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/FaithfulObservationTopology.partitionTopology_eq_discrete_iff_injective`
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/EscapeUnderObservation](EscapeUnderObservation.md)
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/PartitionTopologyKernel](PartitionTopologyKernel.md)
