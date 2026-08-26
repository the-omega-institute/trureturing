# Redundant Coordinate Topology

## Abstract

A joined coordinate changes topology exactly when it is not recoverable.

**Theorem 1.1 (Joining preserves topology exactly for a recoverable coordinate).**

$$\begin{gathered}\forall current: \operatorname{Concept}\left(X, Current\right), candidate: \operatorname{Concept}\left(X, Candidate\right),\\{}([\operatorname{Nonempty}\left(X\right)]) \Rightarrow\\{}(\operatorname{partitionTopology}\left(\operatorname{conceptJoin}\left(current, candidate\right)\right) = \operatorname{partitionTopology}\left(current\right) \iff \operatorname{Refines}\left(candidate, current\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/RedundantCoordinateTopology.join_topology_eq_iff_coordinate_redundant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Joining the current readout with a candidate coordinate records both values. If the candidate is recoverable from the current readout, this adds no new fibers.

Conversely, equality of the joined and current partition topologies makes current-fiber inseparability imply equality of the candidate coordinate.

On the displayed inhabited source, the recovery criterion converts that fiber constancy into Refines candidate current. The theorem claims precisely this biconditional.

**Theorem 1.2 (An unrecoverable coordinate gives exactly a strict join refinement).**

$$\begin{gathered}\forall current: \operatorname{Concept}\left(X, Current\right), candidate: \operatorname{Concept}\left(X, Candidate\right),\\{}([\operatorname{Nonempty}\left(X\right)]) \Rightarrow\\{}((\neg \operatorname{Refines}\left(candidate, current\right)) \iff \operatorname{StrictObservationRefinement}\left(\operatorname{partitionTopology}\left(current\right), \operatorname{partitionTopology}\left(\operatorname{conceptJoin}\left(current, candidate\right)\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/RedundantCoordinateTopology.coordinate_inadequate_iff_strict_join_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joined readout always retains every open set available to the current readout through its first projection.

If the candidate coordinate is not recoverable, equality of the two topologies would contradict the redundancy criterion. Their difference supplies an open set available only after joining.

Conversely, a recoverable coordinate leaves the topologies equal and is incompatible with strict observation refinement. The equivalence retains the Nonempty source instance.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/RedundantCoordinateTopology.coordinate_inadequate_iff_strict_join_refinement`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/RedundantCoordinateTopology.join_topology_eq_iff_coordinate_redundant`
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/ObservationOrderEquivalence](ObservationOrderEquivalence.md)
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/PrimitiveEscapeStrictRefinement](PrimitiveEscapeStrictRefinement.md)
