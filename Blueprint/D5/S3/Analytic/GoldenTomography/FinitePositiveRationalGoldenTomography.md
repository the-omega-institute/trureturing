# Finite Positive-Rational Golden Tomography

## Abstract

Distinct positive rational scales have distinct lifted golden coordinates and admit exact finite moment and time tomography.

**Theorem 1.1 (Lifted golden time windows recover finite rational-scale amplitudes).**

$$\begin{gathered}\forall q: (\forall i, 0 < q_{i}) \land \operatorname{Injective}(q) \Rightarrow\\{}\operatorname{Injective}(\operatorname{firstCrystalTimeWindow}(i \mapsto \operatorname{liftedGoldenRationalNode}(q_{i}))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/FinitePositiveRationalGoldenTomography.finite_positive_rational_golden_time_window_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An injective finite family of positive rational scales remains injective after passage to the existing lifted golden logarithmic coordinate.

Vandermonde tomography then reconstructs the hidden amplitudes exactly. The result concerns the universal-cover coordinate and does not assert quotient-circle conditioning.

## References

- Truth anchor: `D5/S3/Analytic/GoldenTomography/FinitePositiveRationalGoldenTomography.finite_positive_rational_golden_time_window_injective`
- Dependency: [D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography](FiniteVandermondeTomography.md)
- Dependency: [D5/S3/Observer/GoldenCoding/PrimeGoldenScaleCoordinate](../../Observer/GoldenCoding/PrimeGoldenScaleCoordinate.md)
- Dependency: [D5/S3/ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge](../../ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge.md)
