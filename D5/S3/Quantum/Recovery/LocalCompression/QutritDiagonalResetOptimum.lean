/- GID: D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetOptimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetOptimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact pure Bell-source optimum in the diagonal-reset qutrit compression class. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! The stationary characteristic polynomial of the matched Bell block. -/

noncomputable section

namespace D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetOptimum

/-- The characteristic polynomial of the matched block at attenuation amplitude `b`. -/
def characteristic (L b : ℝ) : ℝ :=
  L ^ 3 - L ^ 2 - 3 * L - 1 + 2 * (L + 1) * b - 2 * b ^ 3 - (L - 1) * b ^ 4

/-- Solving the stationarity equation in the spectral parameter. -/
def stationaryLambda (b : ℝ) : ℝ :=
  (-4 * b ^ 3 + 6 * b ^ 2 - 2) / (2 - 4 * b ^ 3)

private theorem stationary_denominator_neg {b : ℝ} (hb : 4 / 5 ≤ b) :
    2 - 4 * b ^ 3 < 0 := by
  have hcube : (4 / 5 : ℝ) ^ 3 ≤ b ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hb _
  linarith

private theorem stationary_lambda_gt_one {b : ℝ} (hb : 4 / 5 ≤ b) (hb' : b ≤ 81 / 100) :
    1 < stationaryLambda b := by
  have hsq : b ^ 2 ≤ (81 / 100 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hb' _
  apply (lt_div_iff_of_neg (stationary_denominator_neg hb)).2
  linarith

/-- The zero at the stationary value has a rationally isolated attenuation amplitude.
At that value the characteristic polynomial is negative at every other amplitude in
`[0,1]`. -/
theorem exists_stationary_characteristic :
    ∃ b : ℝ, 0.80680296 < b ∧ b < 0.80680298 ∧
      1 < stationaryLambda b ∧ characteristic (stationaryLambda b) b = 0 ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ b → characteristic (stationaryLambda b) x < 0 := by
  let l : ℝ := 0.80680296
  let u : ℝ := 0.80680298
  let f : ℝ → ℝ := fun b => characteristic (stationaryLambda b) b
  have hlu : l ≤ u := by norm_num [l, u]
  have hl : 0 < f l := by norm_num [f, l, characteristic, stationaryLambda]
  have hu : f u < 0 := by norm_num [f, u, characteristic, stationaryLambda]
  have hcont : ContinuousOn f (Set.Icc l u) := by
    have hstat : ContinuousOn stationaryLambda (Set.Icc l u) := by
      unfold stationaryLambda
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro b hb
      exact (stationary_denominator_neg ((by norm_num [l] : 4 / 5 ≤ l).trans hb.1)).ne
    unfold f characteristic
    fun_prop
  obtain ⟨b, hb, hroot⟩ := intermediate_value_Icc' hlu hcont
    (show (0 : ℝ) ∈ Set.Icc (f u) (f l) from ⟨hu.le, hl.le⟩)
  have hbl : l < b := lt_of_le_of_ne hb.1 (fun he => hl.ne' (he ▸ hroot))
  have hbu : b < u := lt_of_le_of_ne hb.2 (fun he => hu.ne (he ▸ hroot))
  have hlow := (by norm_num [l] : 4 / 5 ≤ l).trans hb.1
  have hhigh := hb.2.trans (by norm_num [u] : u ≤ 81 / 100)
  have hL := stationary_lambda_gt_one hlow hhigh
  have hs : stationaryLambda b * (2 - 4 * b ^ 3) = -4 * b ^ 3 + 6 * b ^ 2 - 2 :=
    div_mul_cancel₀ _ (stationary_denominator_neg hlow).ne
  have hd : 2 * (stationaryLambda b + 1) - 6 * b ^ 2 -
      4 * (stationaryLambda b - 1) * b ^ 3 = 0 := by
    linear_combination hs
  refine ⟨b, hbl, hbu, hL, hroot, ?_⟩
  intro x hx hxb
  have hTaylor :
      characteristic (stationaryLambda b) x =
        -(x - b) ^ 2 * ((stationaryLambda b - 1) * (x ^ 2 + 2 * x * b + 3 * b ^ 2) +
          2 * x + 4 * b) := by
    change characteristic (stationaryLambda b) b = 0 at hroot
    unfold characteristic at hroot ⊢
    linear_combination hroot + (x - b) * hd
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hlow
  have hcoeff : 0 < (stationaryLambda b - 1) * (x ^ 2 + 2 * x * b + 3 * b ^ 2) +
      2 * x + 4 * b := by positivity
  rw [hTaylor]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hxb))) hcoeff

end D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalResetOptimum
