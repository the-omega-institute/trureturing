# Temporal Fiber Observer Upgrade

## Abstract

Enlarging a time window shrinks observation fibers, and a separated finite mode family is resolved by its first full window.

**Theorem 1.1 (Temporal fibers are antitone in the observation window).**

$$\begin{gathered}\forall m, E, F, x, y: E \subseteq F \land \operatorname{SameTemporalFiber}(m, F, x, y)\\{}\Rightarrow \operatorname{SameTemporalFiber}(m, E, x, y).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/TemporalFiberObserverUpgrade.same_temporal_fiber_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every equality witnessed on a larger finite time window restricts to equality on any smaller window, so adding observation times can only refine the observer kernel.

Under separated finite modes, the first full time window has subsingleton fibers. This records observation-depth refinement without asserting thermodynamic irreversibility.

## References

- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/TemporalFiberObserverUpgrade.same_temporal_fiber_antitone`
- Dependency: [D5/S3/ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge](FiniteCrystalTimeFrequencyBridge.md)
