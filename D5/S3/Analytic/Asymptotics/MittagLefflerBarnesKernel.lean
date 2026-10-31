/- GID: D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The literal Mittag-Leffler Barnes kernel is integrable on exterior contour lines. -/

import D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds
import D5.S3.Analytic.Asymptotics.BarnesSineBounds

open Complex Filter Set MeasureTheory
open scoped Topology Real

noncomputable section
namespace D5.S3.Analytic.Asymptotics.MittagLefflerBarnesKernel

/-- The literal Barnes integrand, with the principal logarithm of `-z`. -/
def kernel (α β : ℝ) (z s : ℂ) : ℂ :=
  Complex.Gamma s * Complex.Gamma (1 - s) *
    (Complex.Gamma ((β : ℂ) - α * s))⁻¹ * Complex.exp (-s * Complex.log (-z))

/-- The positive angular margin in the exterior sector. -/
def margin (α : ℝ) (z : ℂ) : ℝ :=
  Real.pi * (1 - α / 2) - |Complex.arg (-z)|

private theorem reflected (α β : ℝ) (z s : ℂ) :
    kernel α β z s = (Real.pi : ℂ) / Complex.sin (Real.pi * s) *
      (Complex.Gamma ((β : ℂ) - α * s))⁻¹ * Complex.exp (-s * Complex.log (-z)) := by
  rw [kernel, Complex.Gamma_mul_Gamma_one_sub]

private theorem exponential_norm (c y : ℝ) (z : ℂ) :
    ‖Complex.exp (-((c : ℂ) + y * I) * Complex.log (-z))‖ =
      Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.log_re, Complex.log_im]

private theorem sine_pos {c : ℝ} (hc : Real.sin (Real.pi * c) ≠ 0) (y : ℝ) :
    0 < ‖Complex.sin (Real.pi * ((c : ℂ) + y * I))‖ := by
  exact lt_of_lt_of_le
    (mul_pos (div_pos (abs_pos.mpr hc) (by norm_num)) (Real.exp_pos _))
    (BarnesSineBounds.barnesRes_sin_lower_line c y)

/-- A polynomial times the actual sector margin dominates the literal kernel on a vertical line.
The reciprocal Gamma bound applies even where its argument is a Gamma pole. -/
theorem exists_line_majorant {α : ℝ} (hα : 0 < α) (β c : ℝ) (z : ℂ)
    (hc : Real.sin (Real.pi * c) ≠ 0) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ y : ℝ,
      ‖kernel α β z (c + y * I)‖ ≤
        C * (1 + |y|) ^ K * Real.exp (-(margin α z * |y|)) := by
  obtain ⟨A, K, hA⟩ :=
    GammaVerticalReciprocalBounds.exists_norm_recip_Gamma_le |β - α * c|
  have hx : β - α * c ∈ Icc (-|β - α * c|) |β - α * c| :=
    ⟨neg_abs_le _, le_abs_self _⟩
  have hA0 : 0 ≤ A := by
    have h := hA (β - α * c) hx 0
    simp only [abs_zero, add_zero, one_pow, mul_one, mul_zero, zero_div,
      Real.exp_zero] at h
    exact (norm_nonneg _).trans h
  refine ⟨(2 * Real.pi / |Real.sin (Real.pi * c)|) *
    Real.exp (-c * Real.log ‖z‖) * A * (1 + α) ^ K, K, fun y => ?_⟩
  have hsin := BarnesSineBounds.barnesRes_sin_lower_line c y
  have hspos := sine_pos hc y
  have hG := hA (β - α * c) hx (-α * y)
  have harg : (β : ℂ) - α * ((c : ℂ) + y * I) =
      ((β - α * c : ℝ) : ℂ) + I * ((-α * y : ℝ) : ℂ) := by push_cast; ring
  have habs : |(-α * y)| = α * |y| := by rw [abs_mul, abs_neg, abs_of_pos hα]
  rw [habs] at hG
  have hpoly : (1 + α * |y|) ^ K ≤ (1 + α) ^ K * (1 + |y|) ^ K := by
    rw [← mul_pow]
    gcongr
    nlinarith [abs_nonneg y]
  have hangle : y * Complex.arg (-z) ≤ |Complex.arg (-z)| * |y| := by
    calc
      _ ≤ |y * Complex.arg (-z)| := le_abs_self _
      _ = _ := by rw [abs_mul]; ring
  have he : Real.exp (Real.pi * (α * |y|) / 2) *
      Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z)) ≤
        Real.exp (-c * Real.log ‖z‖) *
          Real.exp (Real.pi * |y|) * Real.exp (-(margin α z * |y|)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [margin]
    nlinarith
  rw [reflected, norm_mul, norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, harg, exponential_norm]
  rw [show Real.pi / ‖Complex.sin (Real.pi * ((c : ℂ) + y * I))‖ *
      ‖(Complex.Gamma (((β - α * c : ℝ) : ℂ) + I * ((-α * y : ℝ) : ℂ)))⁻¹‖ *
      Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z)) =
      (Real.pi * ‖(Complex.Gamma
        (((β - α * c : ℝ) : ℂ) + I * ((-α * y : ℝ) : ℂ)))⁻¹‖ *
        Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z))) /
        ‖Complex.sin (Real.pi * ((c : ℂ) + y * I))‖ by ring]
  apply (div_le_iff₀ hspos).2
  have hden : 0 < |Real.sin (Real.pi * c)| := abs_pos.mpr hc
  have hbase :
      Real.pi * ‖(Complex.Gamma
        (((β - α * c : ℝ) : ℂ) + I * ((-α * y : ℝ) : ℂ)))⁻¹‖ *
        Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z)) ≤
      Real.pi * (A * ((1 + α) ^ K * (1 + |y|) ^ K)) *
        (Real.exp (-c * Real.log ‖z‖) * Real.exp (Real.pi * |y|) *
          Real.exp (-(margin α z * |y|))) := by
    calc
      _ ≤ Real.pi * (A * (1 + α * |y|) ^ K *
          Real.exp (Real.pi * (α * |y|) / 2)) *
          Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z)) := by gcongr
      _ = Real.pi * (A * (1 + α * |y|) ^ K) *
          (Real.exp (Real.pi * (α * |y|) / 2) *
            Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z))) := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ _ := hbase
    _ ≤ ((2 * Real.pi / |Real.sin (Real.pi * c)|) *
        Real.exp (-c * Real.log ‖z‖) * A * (1 + α) ^ K * (1 + |y|) ^ K *
        Real.exp (-(margin α z * |y|))) *
        ‖Complex.sin (Real.pi * ((c : ℂ) + y * I))‖ := by
      have hscaled := mul_le_mul_of_nonneg_left hsin
        (by positivity : 0 ≤ (2 * Real.pi / |Real.sin (Real.pi * c)|) *
          Real.exp (-c * Real.log ‖z‖) * A * (1 + α) ^ K * (1 + |y|) ^ K *
          Real.exp (-(margin α z * |y|)))
      convert hscaled using 1 <;> field_simp [hden.ne'] <;> ring

/-- All vertical lines avoiding the sine zeros are integrable in the strict exterior sector. -/
theorem integrable_line {α : ℝ} (hα : 0 < α) (β c : ℝ) (z : ℂ)
    (hc : Real.sin (Real.pi * c) ≠ 0) (hz : 0 < margin α z) :
    Integrable (fun y : ℝ => kernel α β z (c + y * I)) := by
  obtain ⟨C, K, h⟩ := exists_line_majorant hα β c z hc
  have hm : AEStronglyMeasurable (fun y : ℝ => kernel α β z (c + y * I)) := by
    simp_rw [reflected]
    have hrecip := Complex.differentiable_one_div_Gamma.continuous
    fun_prop
  exact ((GammaVerticalReciprocalBounds.integrable_one_add_abs_pow_mul_exp_neg hz K).
    const_mul C).mono' hm (Filter.Eventually.of_forall h)

end D5.S3.Analytic.Asymptotics.MittagLefflerBarnesKernel
