/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleTailMarginalBound
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Eliminate the upper-coordinate marginal from joint mixed-derivative estimates. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailJointScore
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox

/-! A lower bound retaining the dependence on the reflected upper gap. -/

namespace RefinedBMV.PositiveCenter

open private CompactTaylorModel.CompactMiddleBox.gap_lower from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox

/-- The rational lower approximation to the reflected half-logarithmic slope. -/
noncomputable def middleTailMarginalLower (h f : ℝ) : ℝ :=
  let k := 3 + 2 * h
  ((1 + h) * f * (k * f - 4) + 2) / (2 * f * (k * f - 1))

/-- The remainder from replacing the upper-coordinate weight by its leading term is nonnegative. -/
theorem middleTailMarginalLower_le {p : ℕ} (hp : 11 ≤ p) {t : ℝ} (ht : 15 / 4 ≤ t) :
    let h : ℝ := 3 / (p : ℝ)
    middleTailMarginalLower h (upperTailGap h t) ≤ reflectedHalfLogSlope (compositionMoment p 0) t := by
  intro h
  let k := 3 + 2 * h
  let c := (3 + h) * k / 2
  let f := upperTailGap h t
  let x := Real.exp (-t)
  let e := Real.exp (-(k * t))
  let q := (1 + h) * f * (k * f - 4) + 2
  let W := shortGapWeight h t
  have hp₀ : 0 < p := by omega
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp only [h]; positivity
  have hhmax : h ≤ 3 / 11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have ht₀ : 0 < t := by linarith only [ht]
  have hf : 0 < f := tail_gap_pos hh ht₀
  have hc : 0 < c := by dsimp only [c, k]; positivity
  have hW : 0 < W := shortGapWeight_pos hh ht₀
  have hlo : (165 : ℝ) / 89 ≤ f := by
    simpa only [show (15 / 4 : ℝ) / (1 + 3 / 11 * (15 / 4)) = 165 / 89 by norm_num]
      using CompactTaylorModel.CompactMiddleBox.gap_lower hh hhmax (by norm_num) ht
  have hk : 3 ≤ k := by dsimp only [k]; linarith only [hh]
  have hkf : 4 ≤ k * f := by nlinarith only [hlo, mul_nonneg (sub_nonneg.mpr hk) hf.le]
  have hkf₁ : 0 < k * f - 1 := by linarith only [hkf]
  have hq : 2 ≤ q := by
    dsimp only [q]
    have := mul_nonneg (show 0 ≤ (1 + h) * f by positivity) (sub_nonneg.mpr hkf)
    linarith only [this]
  have hx : 0 < x := Real.exp_pos _
  have he : e ≤ x := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg (show 0 ≤ k - 1 by linarith only [hk]) ht₀.le]
  have hj : upperTailSlope h t = f⁻¹ - h := CompactGap.upperTailSlope_eq_inv_gap_sub_rate hh ht₀
  have hb : Real.exp (-(h * t)) = 1 - h * f := by
    have hgap := tail_gap_factor (t := t) hh
    change 1 - Real.exp (-(h * t)) = h * f at hgap
    linarith only [hgap]
  have hClosed := middleTail_reflectedSlope_eq hp₀ ht₀
  change reflectedHalfLogSlope (compositionMoment p 0) t =
    ((1 - 2 * upperTailSlope h t) * (k * f - 1 + e) + k * (Real.exp (-(h * t)) - e)) /
      (2 * W) at hClosed
  have hDef : W = k * f - 1 + e - c * f ^ 2 * x := by
    dsimp only [W, shortGapWeight, f, k, c, e, x]
    ring
  have hdiff : reflectedHalfLogSlope (compositionMoment p 0) t - middleTailMarginalLower h f =
      c * f * (q * x - 2 * e) / (2 * W * (k * f - 1)) := by
    let A := k * f - 1
    have hA : A ≠ 0 := hkf₁.ne'
    rw [hClosed, hj, hb]
    change ((1 - 2 * (f⁻¹ - h)) * (A + e) + k * (1 - h * f - e)) / (2 * W) -
      q / (2 * f * A) = c * f * (q * x - 2 * e) / (2 * W * A)
    field_simp [hf.ne', hW.ne', hA]
    rw [hDef]
    dsimp only [q, A, c, k]
    ring
  have hsign : 0 ≤ q * x - 2 * e := by
    have hqx := mul_le_mul_of_nonneg_right hq hx.le
    linarith only [hqx, he]
  exact sub_nonneg.mp (hdiff.symm ▸ div_nonneg (mul_nonneg (mul_pos hc hf).le hsign)
    (by positivity))

end RefinedBMV.PositiveCenter
