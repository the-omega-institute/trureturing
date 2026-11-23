/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleTailRadicalScalar
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar sign of the radical correction from gap seven halves. -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import D5.S3.Observer.Fluctuation.ThermalCoefficientFloor

/-! The logarithmic decay bound closes the mixed sign of the squared radical difference. -/

namespace RefinedBMV.PositiveCenter

open Set Real

/-- The rational lower bound on the hyperbolic quotient improves the small-width
divided difference of the radical. -/
theorem middleTail_sinh_mul_rational_le {x : ℝ} (hx : 0 < x) :
    (1 + 5 * x ^ 2 / (15 + x ^ 2)) * sinh x ≤ x * cosh x := by
  let f (t : ℝ) := (3 + t ^ 2) * sinh t - 3 * t * cosh t
  let g (t : ℝ) := t * (15 + t ^ 2) * cosh t - (15 + 6 * t ^ 2) * sinh t
  have hf (t : ℝ) : HasDerivAt f (t * (t * cosh t - sinh t)) t := by
    have ht := hasDerivAt_id' t
    have hs := Real.hasDerivAt_sinh t
    have hc := Real.hasDerivAt_cosh t
    apply ((((ht.pow 2).const_add 3).mul hs).sub ((ht.const_mul 3).mul hc)).congr_deriv
    ring
  have hg (t : ℝ) : HasDerivAt g (t * f t) t := by
    have ht := hasDerivAt_id' t
    have hs := Real.hasDerivAt_sinh t
    have hc := Real.hasDerivAt_cosh t
    have h₁ := (ht.mul ((ht.pow 2).const_add 15)).mul hc
    have h₂ := ((((ht.pow 2).const_mul 6).const_add 15).mul hs)
    apply (h₁.sub h₂).congr_deriv
    dsimp only [f]
    ring
  have hfmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t _ ↦ (hf t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (hf t).differentiableAt.differentiableWithinAt)
    intro t ht
    have ht₀ : 0 ≤ t := interior_subset ht
    rw [(hf t).deriv]
    exact mul_nonneg ht₀ (sub_nonneg.mpr
      (D5.S3.Observer.Fluctuation.ThermalCoefficientFloor.sinh_le_self_mul_cosh_of_nonneg ht₀))
  have hgmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t _ ↦ (hg t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (hg t).differentiableAt.differentiableWithinAt)
    intro t ht
    have ht₀ : 0 ≤ t := interior_subset ht
    have hft : 0 ≤ f t := by simpa [f] using hfmono (le_refl 0) ht₀ ht₀
    rw [(hg t).deriv]
    exact mul_nonneg ht₀ hft
  have h : 0 ≤ g x := by simpa [g] using hgmono (le_refl 0) hx.le hx.le
  apply (mul_le_mul_iff_right₀ (show 0 < (15 : ℝ) + x ^ 2 by positivity)).mp
  calc
    _ = (15 + 6 * x ^ 2) * sinh x := by field_simp; ring
    _ ≤ _ := by dsimp only [g] at h; linarith only [h]

/-- The decay comparison bounds the logarithmic slope of the divided difference. -/
theorem middleTail_dividedDifference_lower {u z : ℝ} (hu : 0 < u)
    (hz : (46 / 35 : ℝ) / (1 - exp (-((46 / 35) * u))) ≤ z) :
    1 / u + 23 / 35 ≤ z ∧ (u ≤ 1 → 1 / u + 23 / 35 + 5 * u / 36 ≤ z) := by
  let k : ℝ := 46 / 35
  let x : ℝ := k * u / 2
  have hk : 0 < k := by norm_num [k]
  have hx : 0 < x := by dsimp only [x]; positivity
  have hs := sinh_pos_of_pos hx
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
  change k / (1 - exp (-(k * u))) ≤ z at hz
  rw [hratio] at hz
  have hfrac := (le_div_iff₀ hs).mpr (middleTail_sinh_mul_rational_le hx)
  have hstep := (div_le_div_of_nonneg_right hfrac hu.le)
  have hbase : 1 / u + k / 2 + (5 * x ^ 2 / (15 + x ^ 2)) / u ≤ z := by
    rw [add_div] at hstep
    linarith only [hstep, hz]
  refine ⟨?_, fun hu₁ ↦ ?_⟩
  · have hpos : 0 ≤ (5 * x ^ 2 / (15 + x ^ 2)) / u := by positivity
    dsimp only [k] at hbase
    linarith only [hbase, hpos]
  · have hp : 0 < 15 + x ^ 2 := by positivity
    have hsq : u ^ 2 ≤ 1 := by nlinarith only [hu₁, hu.le, sq_nonneg (u - 1),
      mul_nonneg hu.le (sub_nonneg.mpr hu₁)]
    have hproduct := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hsq)
    have himprove : 5 * u / 36 ≤ (5 * x ^ 2 / (15 + x ^ 2)) / u := by
      apply (le_div_iff₀ hu).mpr
      apply (le_div_iff₀ hp).mpr
      dsimp only [x, k] at hproduct ⊢
      nlinarith only [hproduct, sq_nonneg u]
    dsimp only [k] at hbase
    linarith only [hbase, himprove]

private theorem middleTail_quadratic_pos {u z : ℝ} (hu : 1 / 2 ≤ u)
    (hboost : u ≤ 1 → 1 / u + 23 / 35 + 5 * u / 36 ≤ z) :
    let A := 1 / u + 3 / 2
    0 < 2 * z ^ 2 - 2 * z * (A + 13 / 70) + (3 / 2) * A := by
  let A : ℝ := 1 / u + 3 / 2
  let b : ℝ := 13 / 70
  let F (x : ℝ) := 2 * x ^ 2 - 2 * x * (A + b) + (3 / 2) * A
  have hu' : 0 < u := by linarith
  change 0 < F z
  by_cases hu₁ : u ≤ 1
  · let w : ℝ := 1 / u + 23 / 35 + 5 * u / 36
    have hwz : w ≤ z := hboost hu₁
    have hinv : 1 ≤ 1 / u := (le_div_iff₀ hu').mpr (by simpa using hu₁)
    have hw : A + b ≤ 2 * w := by
      dsimp only [A, b, w]
      linarith only [hinv, hu']
    have hFwz : F w ≤ F z := by
      have h := mul_nonneg (sub_nonneg.mpr hwz) (show 0 ≤ 2 * (z + w - (A + b)) by linarith)
      dsimp only [F]
      nlinarith only [h]
    let t : ℝ := u - 1 / 2
    have ht : 0 ≤ t := sub_nonneg.mpr hu
    have ht₁ : t ≤ 1 / 2 := by dsimp only [t]; linarith
    have ht₂ : 0 ≤ t * (1 / 2 - t) := mul_nonneg ht (sub_nonneg.mpr ht₁)
    have hcalc : u * F w =
        62593 / 6350400 + 1166041 / 1058400 * t - 137 / 3024 * t ^ 2 + 25 / 648 * t ^ 3 := by
      dsimp only [F, w, A, b, t]
      field_simp [hu'.ne']
      <;> ring
    have hwpos : 0 < F w := by
      apply pos_of_mul_pos_right _ hu'.le
      rw [hcalc]
      nlinarith only [ht, ht₂, pow_nonneg ht 3]
    exact hwpos.trans_le hFwz
  · have hA₀ : (3 / 2 : ℝ) ≤ A := by
      dsimp only [A]
      linarith only [one_div_nonneg.mpr hu'.le]
    have hA₁ : A ≤ 5 / 2 := by
      have h : 1 / u ≤ 1 := (div_le_iff₀ hu').mpr (by linarith)
      dsimp only [A]
      linarith
    have hAsq := mul_nonneg (sub_nonneg.mpr hA₁) (show 0 ≤ A by linarith)
    have hbsq : b ^ 2 ≤ (2 / 3) * b ^ 2 * A := by
      dsimp only [b]
      linarith only [hA₀]
    have hdisc : (A + b) ^ 2 < 3 * A := by
      dsimp only [b] at hbsq ⊢
      nlinarith only [hAsq, hbsq, hA₀]
    have hsquare := sq_nonneg (z - (A + b) / 2)
    dsimp only [F]
    nlinarith only [hdisc, hsquare]

/-- A decay rate of `46/35` and the lower divided-difference bounds imply the radical sign. -/
theorem middleTail_radicalScalar_neg {u z y A H kappa eta : ℝ}
    (hu : 1 / 2 ≤ u) (hu₄ : u ≤ 4) (hy : 46 / 35 ≤ y) (hyz : y ≤ z)
    (hz : 1 / u + 23 / 35 ≤ z) (hboost : u ≤ 1 → 1 / u + 23 / 35 + 5 * u / 36 ≤ z)
    (hA : A ≤ 1 / u + 3 / 2) (hH : H ≤ 3 / 2) (hκ : 46 / 35 ≤ kappa) (hη : 0 ≤ eta) :
    (2 * z - A) * H + 2 * (A - z) * y - 2 * kappa * z - eta < 0 := by
  let B : ℝ := 1 / u + 3 / 2
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
        (2 * z - B) * (3 / 2) + 2 * (B - z) * y - 2 * (46 / 35) * z := by
    nlinarith only [hstepA, hstepH, hstepκ, hη]
  apply htop.trans_lt
  by_cases hzB : B ≤ z
  · have h := mul_nonneg (sub_nonneg.mpr hzB) (sub_nonneg.mpr hy)
    have hgap : 0 < 2 * z - B := by
      dsimp only [B]
      linarith only [hz, hinv]
    nlinarith only [h, hgap]
  · have h := mul_nonneg (sub_nonneg.mpr (le_of_not_ge hzB)) (sub_nonneg.mpr hyz)
    have hF := middleTail_quadratic_pos hu hboost
    change 0 < 2 * z ^ 2 - 2 * z * (B + 13 / 70) + (3 / 2) * B at hF
    nlinarith only [h, hF]

end RefinedBMV.PositiveCenter
