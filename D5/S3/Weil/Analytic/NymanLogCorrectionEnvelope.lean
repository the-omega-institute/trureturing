/- GID: D5/S3/Weil/Analytic/NymanLogCorrectionEnvelope
   generality: I
   mirror-B: none(waiver:nyman-signed-prime-support)
   mirror-E: none(waiver:nyman-signed-prime)
   anchors: []
   utility: none
   digest: The logarithmic correction is controlled by a fixed multiple of the earlier power envelope. -/

import D5.S3.Weil.Analytic.NymanLogCorrection
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! A uniform bound for the logarithmic correction at the half exponent and above. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators

namespace NymanLogCorrection

open NymanKernelConvolution (h h_pos)
open NymanPrimeDilations (shell logCorrection)

/-- The kernel correction costs a fixed multiple of the previous-scale envelope. -/
theorem abs_logCorrection_le_envelope {x β M : ℝ} (hx : 0 < x) (hβ : 1 / 2 ≤ β)
    (hM₀ : 0 ≤ M) (hM : ∀ y : ℝ, 0 < y → y ≤ x → |shell y| ≤ M * y ^ β) :
    |logCorrection x| ≤ (4 * h + 16) * M * x ^ β := by
  let E : ℝ := M * x ^ β
  let term (j : ℕ) (v : ℝ) := Real.exp (-(j : ℝ) * v) * shell (x * Real.exp (-v))
  let step (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ) * h
  have hE : 0 ≤ E := mul_nonneg hM₀ (Real.rpow_nonneg hx.le _)
  have hpoint (j : ℕ) {v : ℝ} (hv : 0 ≤ v) :
      |term j v| ≤ E * Real.exp (-(1 / 2 : ℝ) * v) := by
    have hv₁ : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hv)
    have hj₁ : Real.exp (-(j : ℝ) * v) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg j)) hv)
    have hy : |shell (x * Real.exp (-v))| ≤ M * (x * Real.exp (-v)) ^ β :=
      hM _ (mul_pos hx (Real.exp_pos _)) (mul_le_of_le_one_right hx.le hv₁)
    calc
      |term j v| = Real.exp (-(j : ℝ) * v) * |shell (x * Real.exp (-v))| := by
        dsimp only [term]
        rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      _ ≤ 1 * (M * (x * Real.exp (-v)) ^ β) :=
        mul_le_mul hj₁ hy (abs_nonneg _) zero_le_one
      _ = E * Real.exp (-v) ^ β := by
        rw [one_mul, Real.mul_rpow hx.le (Real.exp_nonneg _)]
        dsimp [E]
        ring
      _ ≤ E * Real.exp (-(1 / 2 : ℝ) * v) := by
        rw [show -(1 / 2 : ℝ) * v = -v * (1 / 2 : ℝ) by ring, Real.exp_mul]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge (Real.exp_pos _) hv₁ hβ) hE
  have hIntegral (j : ℕ) : |∫ v in Ioi (0 : ℝ), term j v| ≤ 2 * E := by
    have hhalf : -(1 / 2 : ℝ) < 0 := by norm_num
    have hDom : IntegrableOn (fun v : ℝ => E * Real.exp (-(1 / 2 : ℝ) * v))
        (Ioi (0 : ℝ)) := (integrableOn_exp_mul_Ioi hhalf 0).const_mul E
    have hle := norm_integral_le_of_norm_le
      (f := term j) hDom ((ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun v hv => by
          simpa only [Real.norm_eq_abs] using hpoint j (mem_Ioi.mp hv).le))
    calc
      |∫ v in Ioi (0 : ℝ), term j v| ≤ ∫ v in Ioi (0 : ℝ), E * Real.exp (-(1 / 2 : ℝ) * v) := by
        simpa only [Real.norm_eq_abs] using hle
      _ = 2 * E := by
        rw [integral_const_mul, integral_exp_mul_Ioi hhalf 0]
        norm_num
        <;> ring
  let r := Real.exp (-(h / 2))
  have hr₀ : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (by linarith [h_pos])
  have hden : 0 < 1 - r := sub_pos.mpr hr₁
  have hprod : Real.exp (h / 2) * r = 1 := by
    dsimp [r]
    rw [← Real.exp_add]
    simp
  have hgeomWeight : h * r ≤ 2 * (1 - r) := by
    have hlin := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (h / 2)) hr₀.le
    rw [hprod] at hlin
    nlinarith only [hlin]
  have hSeries (j : ℕ) : |h * (∑' k : ℕ, term j (step k))| ≤ 2 * E := by
    have hGeometric := (hasSum_geometric_of_lt_one hr₀.le hr₁).mul_left (E * r)
    have hbound : |∑' k : ℕ, term j (step k)| ≤ (E * r) * (1 - r)⁻¹ := by
      rw [← Real.norm_eq_abs]
      apply tsum_of_norm_bounded hGeometric
      intro k
      rw [Real.norm_eq_abs]
      have hk : 0 ≤ step k := mul_nonneg (Nat.cast_nonneg _) h_pos.le
      refine (hpoint j hk).trans_eq ?_
      dsimp [step]
      rw [show -(1 / 2 : ℝ) * (((k + 1 : ℕ) : ℝ) * h) =
        ((k + 1 : ℕ) : ℝ) * (-(h / 2)) by ring, Real.exp_nat_mul]
      change E * r ^ (k + 1) = (E * r) * r ^ k
      rw [pow_succ]
      ring
    calc
      |h * (∑' k : ℕ, term j (step k))| = h * |∑' k : ℕ, term j (step k)| := by
        rw [abs_mul, abs_of_pos h_pos]
      _ ≤ h * ((E * r) * (1 - r)⁻¹) := mul_le_mul_of_nonneg_left hbound h_pos.le
      _ = ((h * r) * (1 - r)⁻¹) * E := by ring
      _ ≤ ((2 * (1 - r)) * (1 - r)⁻¹) * E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hgeomWeight
          (inv_nonneg.mpr hden.le)) hE
      _ = 2 * E := by field_simp [hden.ne']
  rw [logCorrection_eq_dilations hx]
  change |4 * h * shell x + ∑ j : Fin 4, (h * (∑' k : ℕ, term j.val (step k)) -
    ∫ v in Ioi (0 : ℝ), term j.val v)| ≤ (4 * h + 16) * M * x ^ β
  calc
    _ ≤ |4 * h * shell x| + |∑ j : Fin 4, (h * (∑' k : ℕ, term j.val (step k)) -
        ∫ v in Ioi (0 : ℝ), term j.val v)| := abs_add_le _ _
    _ ≤ 4 * h * E + ∑ _j : Fin 4, (4 * E) := by
      apply add_le_add
      · have hh : 0 ≤ 4 * h := mul_nonneg (by norm_num) h_pos.le
        rw [abs_mul, abs_of_nonneg hh]
        exact mul_le_mul_of_nonneg_left (hM x hx le_rfl) hh
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (abs_sub _ _).trans ?_
        linarith only [hSeries j.val, hIntegral j.val]
    _ = (4 * h + 16) * M * x ^ β := by
      simp [E, nsmul_eq_mul]
      <;> ring

end NymanLogCorrection
