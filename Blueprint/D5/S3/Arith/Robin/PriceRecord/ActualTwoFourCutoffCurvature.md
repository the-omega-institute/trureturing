# D5 source compiled; RegUNVALIDATED

## Abstract

ActualTwoFourCutoffCurvature

The statements below concern the finite floor mesh and actual two/four cutoff curvature. They do not establish the complete paid-prefix repair or Robin inequality. RegUNVALIDATED: lawful registration, variation and source binding remain unfinished.

The reusable offset is d(j,X)=j log(cutoff j(referencePrice X))-log X. The normalized gain error eta(j,X) is log(gain j(cutoff j(referencePrice X)) * cutoff j(referencePrice X)^j). The transform is F(L,a)=a+log(1+a/L). Its secant theorem requires L>0 and nonnegative endpoints. The normalized gain error tends to zero after multiplication by any fixed natural power of log X, using eventual log X>=0. The original second-order curvature theorem consumes the n=2 specialization; the mixed fourth-order actual-root theorem consumes n=4.

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

**Theorem 1.3 (actual_root_equation).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.actual_root_equation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.actual_root_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem actual_root_equation{j : ℕ} (hj : 2 ≤ j) : ∀ᶠ X : ℝ in atTop, 0 < d j X ∧ 2 < cutoff j (referencePrice X) ∧ F (log X) (d j X) = log (j : ℝ) + η j X

**Theorem 1.4 (scaled_root_error).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.scaled_root_error`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.scaled_root_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem scaled_root_error{j : ℕ} (hj : 2 ≤ j) (n : ℕ) : Tendsto (fun X : ℝ => log X ^ n * η j X) atTop (𝓝 0)

**Theorem 1.5 (F_secant).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.F_secant`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.F_secant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full statement: theorem F_secant{L a b : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b) : ∃ q : ℝ, 1 ≤ q ∧ q ≤ 1 + 1 / L ∧ F L b - F L a = (b - a) * q

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.F_secant`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.actual_root_equation`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.actual_two_four_curvature_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.normalized_gain_bounds`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature.scaled_root_error`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster](FixedLayerShrinkingPrimeRoster.md)
