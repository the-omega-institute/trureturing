# Symmetry-Breaking Observability Gain

## Abstract

Splitting an exact two-mode degeneracy turns a persistent hidden fiber into a faithful two-sample time readout.

**Theorem 1.1 (Mode splitting increases observability).**

$$\begin{gathered}\forall u, v: \mathbb{C}, u \neq v \Rightarrow\\{}\neg \operatorname{Injective}(a \mapsto \operatorname{crystalTimeSample}(\operatorname{degenerateModes}(u), a)) \land\\{}\operatorname{Injective}(\operatorname{firstCrystalTimeWindow}(\operatorname{splitModes}(u, v))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/SymmetryBreakingObservabilityGain.symmetry_breaking_observability_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An exactly degenerate two-mode system has a nontrivial all-time hidden direction, whereas distinct split multipliers make the first two time samples injective.

The theorem captures an information gain caused by lifting spectral degeneracy. It is a finite observer statement and does not assign a physical mechanism to the split.

## References

- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/SymmetryBreakingObservabilityGain.symmetry_breaking_observability_gain`
- Dependency: [D5/S3/ObserverMemory/FourierFibers/DegenerateModeHiddenFiber](DegenerateModeHiddenFiber.md)
- Dependency: [D5/S3/ObserverMemory/FourierFibers/TemporalReflectionBreakVisibility](TemporalReflectionBreakVisibility.md)
