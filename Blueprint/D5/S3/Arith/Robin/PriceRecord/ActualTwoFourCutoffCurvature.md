# D5 source compiled; RegUNVALIDATED

## Abstract

ActualTwoFourCutoffCurvature

The statements below concern the finite floor mesh and actual two/four cutoff curvature. They do not establish the complete paid-prefix repair or Robin inequality. RegUNVALIDATED: lawful registration, variation and source binding remain unfinished.

**Theorem 1.1 (normalized_gain_bounds).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.normalized_gain_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.normalized_gain_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem normalized_gain_bounds {j : ℕ} (hj : 1 ≤ j) {u : ℝ} (hu : 2 ≤ u) :     1 - 1 / u ≤ gain j u * u ^ j ∧ gain j u * u ^ j ≤ 1 ∧       -2 / u ≤ log (gain j u * u ^ j) ∧ log (gain j u * u ^ j) ≤ 0

**Theorem 1.2 (actual_two_four_curvature_tendsto).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.actual_two_four_curvature_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.actual_two_four_curvature_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem actual_two_four_curvature_tendsto :     Tendsto (fun X : ℝ => log X ^ 2 *       ((4 * log (cutoff 4 (referencePrice X)) - log X) -         2 * (2 * log (cutoff 2 (referencePrice X)) - log X)))       atTop (𝓝 (log (2 : ℝ) ^ 2))

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.actual_two_four_curvature_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.normalized_gain_bounds`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster](FixedLayerShrinkingPrimeRoster.md)
