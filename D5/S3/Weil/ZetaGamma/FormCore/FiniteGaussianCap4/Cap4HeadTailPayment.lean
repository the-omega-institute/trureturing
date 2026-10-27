/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4HeadTailPayment
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: The complete signed compact multiplier is paid by the original head and tail square budgets. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4CompactMultiplier
set_option autoImplicit false
noncomputable section
namespace FiniteGaussianCap4

/-- The exact full-square payment used for the physical head/tail split.
The constants are the original L=2/5 and tail debit 44. -/
theorem bounded_multiplier_head_tail_payment (v P T : ℝ) (hv : |v| ≤ 4) :
    -v * P ^ 2 - (2 / 5 : ℝ) * P ^ 2 - 44 * T ^ 2 ≤
      -v * (P + T) ^ 2 := by
  obtain ⟨hvlo, hvhi⟩ := abs_le.mp hv
  by_cases hcross : 0 ≤ 2 * P * T + T ^ 2
  · have hm := mul_nonneg (sub_nonneg.mpr hvhi) hcross
    nlinarith [sq_nonneg (P - 10 * T)]
  · have hm := mul_nonneg (by linarith : 0 ≤ v + 4)
      (neg_nonneg.mpr (le_of_not_ge hcross))
    nlinarith [sq_nonneg (P + 10 * T), sq_nonneg T]

/-- The full compact multiplier has the same unconditional payment. -/
theorem compactDebit_head_tail_payment (x P T : ℝ) :
    -compactDebit x * P ^ 2 - (2 / 5 : ℝ) * P ^ 2 - 44 * T ^ 2 ≤
      -compactDebit x * (P + T) ^ 2 :=
  bounded_multiplier_head_tail_payment (compactDebit x) P T (compactDebit_abs_le_four x)

end FiniteGaussianCap4
