# Observation Order Equivalence

## Abstract

Factorization equals partition-open inclusion; defects are antitone.

**Theorem 1.1 (Readout refinement is exactly partition-open inclusion).**

$$\begin{gathered}\forall coarse: \operatorname{Concept}\left(X, Coarse\right), fine: \operatorname{Concept}\left(X, Fine\right),\\{}([\operatorname{Nonempty}\left(X\right)]) \Rightarrow\\{}(\operatorname{Refines}\left(coarse, fine\right) \iff \operatorname{ObservationOpenInclusion}\left(\operatorname{partitionTopology}\left(coarse\right), \operatorname{partitionTopology}\left(fine\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/ObservationOrderEquivalence.refines_iff_partition_open_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A factorization of the coarse readout through the fine readout pulls every coarse observation-open set into the fine partition topology.

On an inhabited source, the reverse open-set inclusion recovers fiber constancy of the coarse readout along fine fibers and hence a refinement factor.

The equivalence is conditional on the displayed Nonempty source instance; no converse is asserted for an empty source.

**Theorem 1.2 (Target defects are antitone under readout refinement).**

$$\begin{gathered}\forall coarse: \operatorname{Concept}\left(X, Coarse\right), fine: \operatorname{Concept}\left(X, Fine\right),\\{}target: \operatorname{Concept}\left(X, Target\right), refinement: \operatorname{Refines}\left(coarse, fine\right),\\{}\operatorname{defectRelation}\left(fine, target\right) \subseteq \operatorname{defectRelation}\left(coarse, target\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/ObservationOrderEquivalence.defectRelation_antitone_of_refines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the coarse readout factor through the fine readout. Equality of fine observations then implies equality of coarse observations.

A pair that is still indistinguishable to the fine readout while being distinguished by the target is therefore also a defect of the coarse readout.

The conclusion is the displayed one-way subset inclusion; equality of defect relations is not claimed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/ObservationOrderEquivalence.defectRelation_antitone_of_refines`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/ObservationOrderEquivalence.refines_iff_partition_open_inclusion`
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/ResidualSeparationTopology](ResidualSeparationTopology.md)
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/TargetContinuityFactorization](TargetContinuityFactorization.md)
- Dependency: [D5/S3/ConceptDynamics/Topology/ContinuousRefinementObservationTopology](../Topology/ContinuousRefinementObservationTopology.md)
