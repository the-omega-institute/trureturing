# Joint logarithm at the actual Robin clock

## Abstract

Literal Robin floor budgets give a nonzero joint logarithm with inverse-square precision.

**Theorem 1.1 (Eventual nonvanishing and upper bound).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/JointAxis/ActualJointAxisLogarithm.eventually_clock_joint_logarithm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/JointAxis/ActualJointAxisLogarithm.eventually_clock_joint_logarithm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem eventually_clock_joint_logarithm {β κζ : ℝ} (hβ : 37 / 50 ≤ β ∧ β < 3 / 4) (hκζ : 0 < κζ) : ∀ᶠ e : ℤ in atTop, ∀ {Lbar w : ℝ} {h : ℤ} {p : Fin 3 → ℤ}, let R := reference e; let Y := exp R; let K := transportConstant κζ; |R - Lbar| ≤ 1 → 1 ≤ h → (h : ℝ) ≤ exp (R / 50) → jointSquare (boxSizes β κζ Lbar) h p (coordinates Y) w ≤ (43 : ℝ) / 9 → let Ω := omegaThree (h : ℝ) (p 0 : ℝ) (p 1 : ℝ); Ω ≠ 0 ∧ |Ω| ≤ (50 * K + 1) * exp (-(R / 15)) / R ^ 2

The literal floor-budget estimates put the two signed labels in a rectangle around the actual root phases. The third-to-second offset ratio converges to log 3 / log 2, which is strictly inside the integer cone. The root equations reduce the central value to signed cutoff residuals. After the denominator bound is applied, those residuals fit within exp(−R/15)/R². The cubic sensitivity of the first coordinate preserves the inverse-square precision of the second coordinate.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/JointAxis/ActualJointAxisLogarithm.eventually_clock_joint_logarithm`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualModeThreeFloorBudgetTransport](../ActualModeThreeFloorBudgetTransport.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualTwoFourCutoffCurvature](../ActualTwoFourCutoffCurvature.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedBIntegerClock](../FixedBIntegerClock.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm](../JointAxisLogarithm.md)
