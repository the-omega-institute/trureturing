# Degenerate-Mode Hidden Fiber

## Abstract

Equal modal multipliers leave an antisymmetric amplitude invisible at every observation time.

**Theorem 1.1 (Exact degeneracy defeats the full scalar time trace).**

$$\forall z: \mathbb{C}, \neg \operatorname{Injective}(a \mapsto \operatorname{crystalTimeSample}(\operatorname{degenerateModes}(z), a)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/DegenerateModeHiddenFiber.all_time_trace_not_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two equal modal multipliers make the antisymmetric amplitude invisible for every natural observation time, so even the complete scalar time trace is noninjective.

This is a constructive hidden-fiber certificate. It isolates spectral degeneracy as an obstruction that time stacking alone cannot remove.

## References

- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/DegenerateModeHiddenFiber.all_time_trace_not_injective`
- Dependency: [D5/S3/ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge](FiniteCrystalTimeFrequencyBridge.md)
