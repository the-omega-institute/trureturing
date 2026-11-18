/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp cubic sine majorant for the localized Rankin kernel correction. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter
open scoped Topology

namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.KernelLimit

/-- A normalized majorant with the sharp limiting coefficient. -/
def correctionMajorant (s : ℝ) : ℝ :=
  π ^ 2 / (6 * (1 - π ^ 2 / (6 * s ^ 2)))

/-- Cubic sine control retains the sharp one-sixth coefficient. -/
theorem kernel_correction_upper {s : ℝ} (hs : π ≤ s) :
    0 ≤ s * (π / sin (π / s) - s) ∧
      s * (π / sin (π / s) - s) ≤ correctionMajorant s := by
  have hs0 : 0 < s := pi_pos.trans_le hs
  let t : ℝ := π / s
  have ht0 : 0 < t := div_pos pi_pos hs0
  have ht1 : t ≤ 1 := (div_le_one hs0).mpr hs
  have htp : t < π := by dsimp [t]; exact div_lt_self pi_pos (by linarith [pi_gt_three])
  have hsin : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 htp
  have hd : 0 < 1 - t ^ 2 / 6 := by nlinarith
  have hcube := sin_ge_sub_cube ht0.le
  have hquot : t / sin t ≤ 1 / (1 - t ^ 2 / 6) := by
    apply (div_le_div_iff₀ hsin hd).mpr
    nlinarith
  have hnonneg : 0 ≤ t / sin t - 1 := by
    have h := (le_div_iff₀ hsin).mpr (by simpa using sin_le ht0.le)
    linarith
  have hbound : t / sin t - 1 ≤ t ^ 2 / (6 * (1 - t ^ 2 / 6)) := by
    have hid : 1 / (1 - t ^ 2 / 6) - 1 =
        t ^ 2 / (6 * (1 - t ^ 2 / 6)) := by
      field_simp [hd.ne']
      <;> ring
    linarith
  have hid : s * (π / sin (π / s) - s) = s ^ 2 * (t / sin t - 1) := by
    dsimp [t]
    field_simp [hs0.ne', hsin.ne']
    <;> ring
  rw [hid]
  constructor
  · exact mul_nonneg (sq_nonneg _) hnonneg
  · have hb := mul_le_mul_of_nonneg_left hbound (sq_nonneg s)
    convert hb using 1
    dsimp only [correctionMajorant, t]
    field_simp [hs0.ne']
    <;> ring

/-- The correction majorant approaches the sharp coefficient pi squared over six. -/
theorem correction_majorant_limit :
    Tendsto correctionMajorant atTop (𝓝 (π ^ 2 / 6)) := by
  have hi : Tendsto (fun s : ℝ => 1 / s) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop 1
  have h := tendsto_const_nhds.div
    ((tendsto_const_nhds.sub ((hi.pow 2).const_mul (π ^ 2 / 6))).const_mul 6)
    (by norm_num : (1 - π ^ 2 / 6 * 0 ^ 2) * 6 ≠ 0)
  norm_num only [zero_pow, mul_zero, sub_zero, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  dsimp only [correctionMajorant]
  field_simp [hs.ne']
  <;> ring

end D5.S3.Arith.Robin.Analytic.OmegaSecond.KernelLimit
