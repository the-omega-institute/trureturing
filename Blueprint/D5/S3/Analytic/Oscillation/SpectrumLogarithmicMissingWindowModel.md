# An Infinite Spectrum for the Logarithmic Waiting Gain

## Abstract

Fourth-root bins realize the logarithmic square-tail bound.

**Theorem 1.1 (An infinite model for the logarithmic waiting gain).**

$$\exists S \in Spectrum,\; \exists w \in \operatorname{index}\left(S\right) \to \mathbb{R},\; \operatorname{Infinite}\left(\operatorname{index}\left(S\right)\right) \land \left(\left(\forall j \in \operatorname{index}\left(S\right),\; 0 < \operatorname{w}\left(j\right)\right) \land \left(\operatorname{LinearIndependent}\left(\mathbb{Q}, \operatorname{gamma}\left(S\right)\right) \land \left(\operatorname{HasLogSquaredMass}\left(S, w\right) \land \operatorname{HasLogarithmicSquareTail}\left(S, w\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindowModel.exists_infinite_logarithmic_model` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the same rationally independent fourth-root bins and strictly positive weights. Their square tail is at most B/X² for a fixed B > 0 whenever X ≥ 1. Once log X ≥ 1, this is at most B log X/X uniformly in T ≥ X. `D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindowModel.exists_infinite_critical_model``D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindow.eventual_logarithmic_missing_window`

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindowModel.exists_infinite_critical_model`
- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindow.eventual_logarithmic_missing_window`
- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindowModel.exists_infinite_logarithmic_model`
- Dependency: [D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindowModel](SpectrumCriticalMissingWindowModel.md)
- Dependency: [D5/S3/Analytic/Oscillation/SpectrumLogarithmicMissingWindow](SpectrumLogarithmicMissingWindow.md)
