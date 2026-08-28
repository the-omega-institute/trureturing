# Target Continuity Factorization

## Abstract

On an inhabited source, recoverability is continuity into the discrete target.

**Theorem 1.1 (Target recovery is continuity from the partition topology).**

$$\begin{gathered}\forall readout: \operatorname{Concept}\left(X, Coordinate\right), target: \operatorname{Concept}\left(X, Target\right),\\{}\operatorname{Nonempty}\left(X\right) \Rightarrow\\{}(\operatorname{Refines}\left(target, readout\right) \iff \operatorname{Continuous}\left(\operatorname{partitionTopology}\left(readout\right), \operatorname{bottomTopology}\left(Target\right), target\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/TargetContinuityFactorization.target_factors_iff_continuous_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Refines target readout means that a recovery map reconstructs the target from the displayed readout.

Such a factorization makes the target constant on every readout fiber. Conversely, inhabitedness and the target recovery criterion turn fiber constancy into a recovery factor.

For the partition topology on the source and the bottom topology on the target, continuity is exactly that same fiber-constancy law.

The displayed biconditional therefore retains the Lean theorem's Nonempty source hypothesis and its discrete target topology.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/TargetContinuityFactorization.target_factors_iff_continuous_partition`
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/PartitionTopologyKernel](PartitionTopologyKernel.md)
- Dependency: [D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion](../Restoration/TargetRecoveryCriterion.md)
