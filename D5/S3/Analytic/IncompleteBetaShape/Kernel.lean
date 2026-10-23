/- GID: D5/S3/Analytic/IncompleteBetaShape/Kernel
   generality: G
   mirror-B: D5/B/S3/Analytic/IncompleteBetaShape/Kernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric sliding beta kernels and their strict midpoint monotonicity. -/

import D5.S3.Analytic.KummerRatio.BetaIntegral

/-! Sliding averages of a symmetric beta weight. -/

noncomputable section
open Set MeasureTheory
open scoped Real

namespace D5.S3.Analytic.IncompleteBetaShape.Kernel

/-- The symmetric beta weight. -/
def w (b y : ℝ) : ℝ := (y * (1 - y)) ^ (b - 1)

/-- Uniform average of the beta weight on an affine interval. -/
def F (b s v : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, w b (s * v + (1 - s) * u)

/-- Average over the beta distribution with shapes c and n+2. -/
def H (c : ℝ) (n : ℕ) (b v : ℝ) : ℝ :=
  (Real.Gamma c * Real.Gamma ((n : ℝ) + 2) / Real.Gamma (c + n + 2))⁻¹ *
    ∫ s in (0 : ℝ)..1,
      s ^ (c - 1) * (1 - s) ^ ((n : ℝ) + 1) * F b s v

private lemma w_nonneg (b : ℝ) {y : ℝ} (hy : y ∈ Icc 0 1) : 0 ≤ w b y :=
  Real.rpow_nonneg (mul_nonneg hy.1 (sub_nonneg.mpr hy.2)) _

private lemma w_symm (b y : ℝ) : w b (1-y) = w b y := by
  unfold w
  congr 1
  ring

private lemma w_integrable {b : ℝ} (hb : 0 < b) :
    IntervalIntegrable (w b) volume 0 1 := by
  apply (D5.S3.Analytic.KummerRatio.BetaIntegral.intervalIntegrable_beta hb hb).congr
  intro y hy
  rw [Set.uIoc_of_le zero_le_one] at hy
  exact (Real.mul_rpow hy.1.le (sub_nonneg.mpr hy.2)).symm

private lemma integral_w {b : ℝ} (hb : 0 < b) :
    (∫ y in (0:ℝ)..1, w b y) = Real.Gamma b * Real.Gamma b / Real.Gamma (2*b) := by
  rw [show 2*b = b+b by ring,
    ← D5.S3.Analytic.KummerRatio.BetaIntegral.integral_beta hb hb]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro y hy
  exact Real.mul_rpow hy.1.le (sub_nonneg.mpr hy.2.le)

private lemma F_eq_window (b s v : ℝ) (hs : s ≠ 1) :
    F b s v = (1-s)⁻¹ * ∫ y in s*v..s*v+1-s, w b y := by
  unfold F
  rw [intervalIntegral.integral_comp_add_mul _ (sub_ne_zero.mpr hs.symm)]
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul]
  congr 2
  ring

/-- Reflection in the midpoint preserves the affine uniform average. -/
theorem F_symm (b s v : ℝ) : F b s (1-v) = F b s v := by
  have he : (fun u => w b (s*(1-v)+(1-s)*u)) =
      fun u => w b (s*v+(1-s)*(1-u)) := by
    funext u
    rw [← w_symm b (s*v+(1-s)*(1-u))]
    congr 1
    ring
  unfold F
  rw [he]
  have hr := intervalIntegral.integral_comp_sub_left
    (fun u => w b (s*v+(1-s)*u)) (a := (0:ℝ)) (b := 1) 1
  simpa using hr

/-- Reflection in the midpoint preserves the beta averaged kernel. -/
theorem H_symm (c : ℝ) (n : ℕ) (b v : ℝ) : H c n b (1-v) = H c n b v := by
  unfold H
  simp only [F_symm]

end D5.S3.Analytic.IncompleteBetaShape.Kernel
