/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleTailRadicalScalar
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar sign of the radical correction from gap thirteen fourths. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import D5.S3.Observer.Fluctuation.ThermalCoefficientFloor

/-! The logarithmic decay bound closes the mixed sign of the squared radical difference. -/

namespace RefinedBMV.PositiveCenter

open Set Real

/-- The exponential decay comparison gives a lower divided-difference slope. -/
theorem middleTail_dividedDifference_lower {u z : ℝ} (hu : 0 < u)
    (hz : (31 / 25 : ℝ) / (1 - exp (-((31 / 25) * u))) ≤ z) :
    1 / u + 31 / 50 ≤ z := by
  let k : ℝ := 31 / 25
  let x : ℝ := k * u / 2
  have hk : 0 < k := by norm_num [k]
  have hx : 0 < x := by dsimp only [x]; positivity
  have hs : 0 < sinh x := Real.sinh_pos_iff.mpr hx
  have he : 0 < exp x - exp (-x) := sub_pos.mpr (exp_lt_exp.mpr (by linarith))
  have hexp : exp (-(k * u)) = exp (-x) / exp x := by
    rw [← exp_sub]
    congr 1
    dsimp only [x]
    ring
  have hratio : k / (1 - exp (-(k * u))) = k / 2 + (x * cosh x / sinh x) / u := by
    rw [hexp, cosh_eq, sinh_eq]
    have hdiff : (exp x - exp (-x)) / 2 ≠ 0 := (div_pos he (by norm_num)).ne'
    field_simp [hu.ne', (exp_pos x).ne', he.ne', hdiff]
    dsimp only [x]
    ring
  have hfrac : 1 ≤ x * cosh x / sinh x := (le_div_iff₀ hs).mpr (by
    rw [one_mul]
    exact D5.S3.Observer.Fluctuation.ThermalCoefficientFloor.sinh_le_self_mul_cosh_of_nonneg hx.le)
  have hstep := div_le_div_of_nonneg_right hfrac hu.le
  change k / (1 - exp (-(k * u))) ≤ z at hz
  rw [hratio] at hz
  dsimp only [k] at hz
  linarith only [hstep, hz]

private theorem middleTail_quadratic_pos {u z : ℝ} (hu : 1 / 2 ≤ u) (hu₄ : u ≤ 4)
    (hz : 1 / u + 31 / 50 ≤ z) :
    let A := 1 / u + 13 / 10
    0 < 2 * z ^ 2 - 2 * z * (A + 13 / 50) + (3 / 2) * A := by
  let A : ℝ := 1 / u + 13 / 10
  let w : ℝ := 1 / u + 31 / 50
  let b : ℝ := 13 / 50
  let F (x : ℝ) := 2 * x ^ 2 - 2 * x * (A + b) + (3 / 2) * A
  change 0 < F z
  have hu' : 0 < u := by linarith
  have hinv : (1 / 4 : ℝ) ≤ 1 / u := one_div_le_one_div_of_le hu' hu₄
  have hinv₂ : 1 / u ≤ 2 := (div_le_iff₀ hu').mpr (by linarith only [hu])
  have hw : -(7 / 100 : ℝ) ≤ 2 * w - (A + b) := by
    dsimp only [A, b, w]
    linarith only [hinv]
  have hFw : F w = 1961 / 2500 - (19 / 50) * (1 / u) := by
    dsimp only [F, A, b, w]
    ring
  have hmargin : (61 / 2500 : ℝ) ≤ F w := by
    rw [hFw]
    linarith only [hinv₂]
  have hwz : w ≤ z := hz
  have hdiff := mul_nonneg (sub_nonneg.mpr hwz)
    (show 0 ≤ 2 * (2 * w - (A + b)) + 7 / 50 by linarith only [hw])
  have he : F z - F w =
      2 * (z - w) ^ 2 + (z - w) * (2 * (2 * w - (A + b))) := by
    dsimp only [F]
    ring
  nlinarith only [hmargin, he, hdiff, sq_nonneg (z - w - 7 / 200)]

/-- A decay rate of `31/25` and the lower divided-difference bounds imply the radical sign. -/
theorem middleTail_radicalScalar_neg {u z y A H kappa eta : ℝ}
    (hu : 1 / 2 ≤ u) (hu₄ : u ≤ 4) (hy : 31 / 25 ≤ y) (hyz : y ≤ z)
    (hz : 1 / u + 31 / 50 ≤ z)
    (hA : A ≤ 1 / u + 13 / 10) (hH : H ≤ 3 / 2) (hκ : 31 / 25 ≤ kappa) (hη : 0 ≤ eta) :
    (2 * z - A) * H + 2 * (A - z) * y - 2 * kappa * z - eta < 0 := by
  let B : ℝ := 1 / u + 13 / 10
  have hu' : 0 < u := by linarith
  have hinv : (1 / 4 : ℝ) ≤ 1 / u := one_div_le_one_div_of_le hu' hu₄
  have hz₀ : 0 ≤ z := by linarith only [hy, hyz]
  have hB : 0 ≤ 2 * z - B := by
    dsimp only [B]
    linarith only [hz, hinv]
  have hAH : 0 ≤ 2 * y - H := by linarith only [hy, hH]
  have hA' : 0 ≤ B - A := sub_nonneg.mpr hA
  have hstepA := mul_nonneg hA' hAH
  have hstepH := mul_nonneg hB (sub_nonneg.mpr hH)
  have hstepκ := mul_nonneg (sub_nonneg.mpr hκ) hz₀
  have htop :
      (2 * z - A) * H + 2 * (A - z) * y - 2 * kappa * z - eta ≤
        (2 * z - B) * (3 / 2) + 2 * (B - z) * y - 2 * (31 / 25) * z := by
    nlinarith only [hstepA, hstepH, hstepκ, hη]
  apply htop.trans_lt
  by_cases hzB : B ≤ z
  · have h := mul_nonneg (sub_nonneg.mpr hzB) (sub_nonneg.mpr hy)
    have hgap : 0 < 2 * z - B := by
      dsimp only [B]
      linarith only [hz, hinv]
    nlinarith only [h, hgap]
  · have h := mul_nonneg (sub_nonneg.mpr (le_of_not_ge hzB)) (sub_nonneg.mpr hyz)
    have hF := middleTail_quadratic_pos hu hu₄ hz
    change 0 < 2 * z ^ 2 - 2 * z * (B + 13 / 50) + (3 / 2) * B at hF
    nlinarith only [h, hF]

end RefinedBMV.PositiveCenter
