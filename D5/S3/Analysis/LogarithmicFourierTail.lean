/- GID: D5/S3/Analysis/LogarithmicFourierTail
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-profile-fourier4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourier integration of the decaying tail of the hyperbolic logarithm. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
Omega original.

Fourier integration of the decaying tail of the hyperbolic logarithm.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open scoped ENNReal

namespace Omega

private def decayRate (k : ℕ) : ℝ := 2 * Real.pi * ((k : ℝ) + 1)

private theorem decayRate_pos (k : ℕ) : 0 < decayRate k := by
  unfold decayRate
  positivity

private def logTerm (k : ℕ) (s : ℝ) : ℝ :=
  Real.exp (-decayRate k * |s|) / ((k : ℝ) + 1)

private theorem logTail_series {s : ℝ} (hs : s ≠ 0) :
    HasSum (fun k : ℕ => logTerm k s) (-Real.log (1 - Real.exp (-2 * Real.pi * |s|))) := by
  have hx : |Real.exp (-2 * Real.pi * |s|)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (by linarith [Real.pi_pos]) (abs_pos.mpr hs)
  refine (Real.hasSum_pow_div_log_of_abs_lt_one hx).congr_fun fun k => ?_
  simp only [logTerm, decayRate, Nat.cast_add, Nat.cast_one, ← Real.exp_nat_mul]
  congr 2
  ring

private def exponentialMode (d ν s : ℝ) : ℂ :=
  Complex.exp (((-d * |s| : ℝ) : ℂ) - Complex.I * (ν : ℂ) * s)

private theorem exponentialMode_integrable {d : ℝ} (hd : 0 < d) (ν : ℝ) :
    Integrable (exponentialMode d ν) := by
  have hi : Integrable (fun s : ℝ => Real.exp (-d * |s|)) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    refine ((integrableOn_exp_mul_Iic hd 0).congr_fun ?_ measurableSet_Iic).union
      ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) 0).congr_fun ?_ measurableSet_Ioi)
    · intro s hs
      simp only [abs_of_nonpos (mem_Iic.mp hs), neg_mul_neg]
    · intro s hs
      simp only [abs_of_pos (mem_Ioi.mp hs)]
  have hc : Continuous (exponentialMode d ν) := by unfold exponentialMode; fun_prop
  refine hi.mono' hc.aestronglyMeasurable ?_
  filter_upwards with s
  simp [exponentialMode, Complex.norm_exp, Complex.sub_re, Complex.mul_re]

private theorem exponentialMode_integral {d : ℝ} (hd : 0 < d) (ν : ℝ) :
    (∫ s : ℝ, exponentialMode d ν s) = ((2 * d / (d ^ 2 + ν ^ 2) : ℝ) : ℂ) := by
  let negSide : ℂ := (d : ℂ) - Complex.I * ν
  let posSide : ℂ := -(d : ℂ) - Complex.I * ν
  have hneg : 0 < negSide.re := by simpa [negSide, Complex.sub_re, Complex.mul_re] using hd
  have hpos : posSide.re < 0 := by simpa [posSide, Complex.sub_re, Complex.mul_re] using hd
  have h₁ : (∫ s in Iic (0 : ℝ), exponentialMode d ν s) =
      ∫ s : ℝ in Iic 0, Complex.exp (negSide * s) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro s hs
    unfold exponentialMode negSide
    rw [abs_of_nonpos hs]
    push_cast
    congr 1
    ring
  have h₂ : (∫ s in Ioi (0 : ℝ), exponentialMode d ν s) =
      ∫ s : ℝ in Ioi 0, Complex.exp (posSide * s) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    unfold exponentialMode posSide
    rw [abs_of_pos hs]
    push_cast
    congr 1
    ring
  rw [← integral_add_compl measurableSet_Iic (exponentialMode_integrable hd ν),
    compl_Iic, h₁, h₂, integral_exp_mul_complex_Iic hneg, integral_exp_mul_complex_Ioi hpos]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  have hdn : (d : ℂ) ^ 2 + (ν : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show d ^ 2 + ν ^ 2 ≠ 0 by positivity)
  have hn : negSide ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at hneg
    exact (lt_irrefl 0) hneg
  have hp : posSide ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at hpos
    exact (lt_irrefl 0) hpos
  field_simp [hn, hp, hdn]
  dsimp [negSide, posSide]
  linear_combination -(2 * (d : ℂ) * (ν : ℂ) ^ 2) * Complex.I_sq

/-- The integrable logarithmic tail after removing the linear term of the hyperbolic logarithm. -/
def logTail (s : ℝ) : ℂ :=
  (-Real.log (1 - Real.exp (-2 * Real.pi * |s|)) : ℝ)

/-- The angular Fourier integral of the logarithmic tail is its rational mode series. -/
theorem logarithmic_mode_integral (ν : ℝ) :
    (∫ s : ℝ, Complex.exp (-Complex.I * (ν : ℂ) * s) * logTail s) =
      ∑' k : ℕ, ((4 * Real.pi / ((2 * Real.pi * ((k : ℝ) + 1)) ^ 2 + ν ^ 2) : ℝ) : ℂ) := by
  let f : ℕ → ℝ → ℂ := fun k s => exponentialMode (decayRate k) ν s / ((k : ℂ) + 1)
  have hi (k : ℕ) : Integrable (f k) :=
    (exponentialMode_integrable (decayRate_pos k) ν).div_const _
  have hnorm (k : ℕ) (s : ℝ) : ‖f k s‖ = logTerm k s := by
    dsimp only [f]
    rw [norm_div, ← Complex.ofReal_natCast, ← Complex.ofReal_one,
      ← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    simp [exponentialMode, logTerm, Complex.norm_exp, Complex.sub_re, Complex.mul_re]
  have hvol (k : ℕ) :
      (∫ s : ℝ, ‖f k s‖) = (1 / Real.pi) * (((k : ℝ) + 1) ^ 2)⁻¹ := by
    simp_rw [hnorm, logTerm, integral_div]
    rw [integral_comp_abs (f := fun s => Real.exp (-decayRate k * s)),
      integral_exp_mul_Ioi (show -decayRate k < 0 by linarith [decayRate_pos k])]
    simp only [mul_zero, Real.exp_zero, div_neg, neg_div, neg_neg, decayRate]
    field_simp [Real.pi_ne_zero]
  have hsum : Summable (fun k => ∫ s : ℝ, ‖f k s‖) := by
    simp_rw [hvol, ← one_div]
    apply Summable.mul_left
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).2 ((Real.summable_one_div_nat_pow).2 (by norm_num : 1 < (2 : ℕ))))
  have hne : ∀ᵐ s : ℝ, s ≠ 0 := by
    rw [ae_iff]
    simp
  calc
    _ = ∫ s : ℝ, ∑' k, f k s := by
      apply integral_congr_ae
      filter_upwards [hne] with s hs
      have H := (Complex.ofRealCLM.hasSum (logTail_series hs)).mul_left
        (Complex.exp (-Complex.I * (ν : ℂ) * s))
      change Complex.exp (-Complex.I * (ν : ℂ) * s) *
        Complex.ofRealCLM (-Real.log (1 - Real.exp (-2 * Real.pi * |s|))) = _
      rw [← H.tsum_eq]
      congr 1
      ext k
      simp only [Complex.ofRealCLM_apply, f, logTerm, exponentialMode, Complex.ofReal_div,
        Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_exp,
        Complex.exp_sub]
      simp only [div_eq_mul_inv, ← Complex.exp_neg]
      simp only [neg_mul]
      ring
    _ = ∑' k, ∫ s : ℝ, f k s := (integral_tsum_of_summable_integral_norm hi hsum).symm
    _ = _ := by
      congr 1
      ext k
      dsimp only [f]
      rw [integral_div, exponentialMode_integral (decayRate_pos k)]
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_add,
        Complex.ofReal_mul, Complex.ofReal_ofNat]
      unfold decayRate
      push_cast
      have hk' : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast hk
      field_simp [hk']
      ring


/-- The decaying logarithmic tail is integrable on the real line. -/
theorem integrable_logTail : Integrable logTail := by
  let f : ℕ → ℝ → ℂ := fun k s => exponentialMode (decayRate k) 0 s / ((k : ℂ) + 1)
  have hi (k : ℕ) : Integrable (f k) :=
    (exponentialMode_integrable (decayRate_pos k) 0).div_const _
  have hnorm (k : ℕ) (s : ℝ) : ‖f k s‖ = logTerm k s := by
    dsimp only [f]
    rw [norm_div, ← Complex.ofReal_natCast, ← Complex.ofReal_one,
      ← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    simp [exponentialMode, logTerm, Complex.norm_exp, Complex.sub_re, Complex.mul_re]
  have hsum : Summable (fun k => ∫ s : ℝ, ‖f k s‖) := by
    have hvol (k : ℕ) : (∫ s : ℝ, ‖f k s‖) = (1 / Real.pi) * (((k : ℝ) + 1) ^ 2)⁻¹ := by
      simp_rw [hnorm, logTerm, integral_div]
      rw [integral_comp_abs (f := fun s => Real.exp (-decayRate k * s)),
        integral_exp_mul_Ioi (show -decayRate k < 0 by linarith [decayRate_pos k])]
      simp only [mul_zero, Real.exp_zero, div_neg, neg_div, neg_neg, decayRate]
      field_simp [Real.pi_ne_zero]
    simp_rw [hvol, ← one_div]
    exact Summable.mul_left _ (by simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).2 ((Real.summable_one_div_nat_pow).2 (by norm_num : 1 < (2 : ℕ)))))
  have hlog : Measurable logTail := by unfold logTail; fun_prop
  refine ⟨hlog.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hne : ∀ᵐ s : ℝ, s ≠ 0 := by rw [ae_iff]; simp
  have heq : (fun s => ‖logTail s‖ₑ) =ᵐ[volume] fun s => ∑' k, ‖f k s‖ₑ := by
    filter_upwards [hne] with s hs
    have h := logTail_series hs
    have hp (k : ℕ) : 0 ≤ logTerm k s := by unfold logTerm; positivity
    have hval := h.tsum_eq
    have hn : 0 ≤ ∑' k : ℕ, logTerm k s := tsum_nonneg hp
    change ‖logTail s‖ₑ = _
    rw [show ‖logTail s‖ₑ = ENNReal.ofReal (-Real.log (1 - Real.exp (-2 * Real.pi * |s|))) by
      rw [← ofReal_norm, logTail, Complex.norm_real, Real.norm_of_nonneg (hval ▸ hn)]]
    rw [← hval, ENNReal.ofReal_tsum_of_nonneg hp h.summable]
    congr with k
    rw [← ofReal_norm, hnorm]
  rw [lintegral_congr_ae heq, lintegral_tsum (fun k => (hi k).aestronglyMeasurable.enorm)]
  have hterm (k : ℕ) : (∫⁻ s : ℝ, ‖f k s‖ₑ) = ENNReal.ofReal (∫ s : ℝ, ‖f k s‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hi k).norm (.of_forall fun _ => norm_nonneg _)]
    simp only [ofReal_norm]
  simp_rw [hterm]
  exact hsum.tsum_ofReal_lt_top

/-- The hyperbolic logarithm splits into its linear distance and decaying tail. -/
theorem log_two_abs_sinh (s : ℝ) (hs : s ≠ 0) :
    (Real.log (2 * |Real.sinh (Real.pi * s)|) : ℂ) =
      ((Real.pi * |s| : ℝ) : ℂ) - logTail s := by
  let y := Real.pi * |s|
  have hy : 0 < y := mul_pos Real.pi_pos (abs_pos.mpr hs)
  have hsinh : |Real.sinh (Real.pi * s)| = Real.sinh y := by
    rcases lt_or_gt_of_ne hs with hn | hp
    · rw [abs_of_neg (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg Real.pi_pos hn))]
      rw [show y = -(Real.pi * s) by dsimp [y]; rw [abs_of_neg hn, mul_neg]]
      rw [Real.sinh_neg]
    · rw [abs_of_pos (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hp))]
      simp [y, abs_of_pos hp]
  have he : 2 * Real.sinh y = Real.exp y * (1 - Real.exp (-2 * y)) := by
    rw [Real.sinh_eq, mul_sub, mul_one, ← Real.exp_add,
      show y + -2 * y = -y by ring]
    ring
  rw [hsinh, he, Real.log_mul (Real.exp_ne_zero _) (sub_ne_zero.mpr
    ((Real.exp_lt_one_iff.mpr (by linarith : -2 * y < 0)).ne.symm)), Real.log_exp]
  unfold logTail
  rw [show -2 * y = -2 * Real.pi * |s| by dsimp [y]; ring]
  dsimp [y]
  push_cast
  ring

end Omega
