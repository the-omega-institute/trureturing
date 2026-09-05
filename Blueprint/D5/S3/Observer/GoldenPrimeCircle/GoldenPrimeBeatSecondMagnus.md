# Golden Prime Beat Second-Magnus Separation

## Abstract

The golden long-short frequency gap is log p, so pi divided by log p maximizes the alternating two-slot Magnus kernel and twice that time restores resonance.

**Theorem 1.1 (Half-beat separation and full-beat recurrence).**

$$\lvert\operatorname{secondMagnusSwapKernel}\rvert = 2, \operatorname{fullBeatKernel} = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenPrimeBeatSecondMagnus.prime_beat_separation_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The deterministic alphabet frequencies phi log p and phi squared log p differ by exactly log p. At time pi divided by log p their relative phase is minus one, and the alternating kernel reaches its universal norm-two bound.

At twice that time the relative phase completes a full turn and the kernel vanishes. The calibration is prime dependent and does not provide one common window for an infinite prime family.

## References

- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenPrimeBeatSecondMagnus.prime_beat_separation_recurrence`
- Dependency: [D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature](../AgencyHolonomy/SecondMagnusSwapCurvature.md)
- Dependency: [D5/S3/Observer/GoldenPrimeCircle/GoldenEulerStepPhaseLaw](GoldenEulerStepPhaseLaw.md)
