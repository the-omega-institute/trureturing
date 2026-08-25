# Multi-Target Observation Topology

## Abstract

Joint-target continuity and separation deficits decompose into component targets.

**Theorem 1.1 (Joint-target continuity is exactly componentwise continuity).**

$$\begin{gathered}\forall readout: \operatorname{Concept}\left(X, Coordinate\right),\\{}targets: (\forall index: Index, \operatorname{Concept}\left(X, Target(index)\right)),\\{}\operatorname{Continuous}\left(\operatorname{partitionTopology}\left(readout\right), \operatorname{bottomTopology}\left((\forall index: Index, Target(index))\right), \operatorname{jointTarget}\left(targets\right)\right) \iff (\forall index: Index, \operatorname{Continuous}\left(\operatorname{partitionTopology}\left(readout\right), \operatorname{bottomTopology}\left(Target(index)\right), targets(index)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/MultiTargetObservationTopology.jointTarget_continuous_iff_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A dependent joint target records every indexed target value at once. Continuity from the readout partition therefore forces each coordinate target to be continuous.

Conversely, componentwise continuity makes every target constant on each readout fiber. Function extensionality then makes the whole dependent tuple constant on that fiber.

Both sides use the bottom topology on the relevant target carrier; no finiteness or inhabitedness condition on the index is asserted.

**Theorem 1.2 (The joint-target deficit is the union of component deficits).**

$$\begin{gathered}\forall current: \operatorname{Concept}\left(X, Current\right),\\{}targets: (\forall index: Index, \operatorname{Concept}\left(X, Target(index)\right)),\\{}\operatorname{separationDeficit}\left(current, \operatorname{jointTarget}\left(targets\right)\right) = \operatorname{iUnion}\left(index: Index, \operatorname{separationDeficit}\left(current, targets(index)\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/MultiTargetObservationTopology.jointTarget_separationDeficit_eq_iUnion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pair lies in the joint separation deficit when the current readout identifies it but the dependent target tuple distinguishes it.

Two dependent tuples differ exactly when some indexed coordinate differs. The same pair therefore lies in at least one component separation deficit.

Extensionality yields equality with the indexed union, not merely one inclusion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/MultiTargetObservationTopology.jointTarget_continuous_iff_components`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/MultiTargetObservationTopology.jointTarget_separationDeficit_eq_iUnion`
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/PartitionTopologyKernel](PartitionTopologyKernel.md)
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/ResidualSeparationTopology](ResidualSeparationTopology.md)
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/TargetContinuityFactorization](TargetContinuityFactorization.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/MultiTargetMinimalSufficiency](../Refinement/MultiTargetMinimalSufficiency.md)
