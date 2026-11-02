/- GID: D5/S3/Arith/ModularForms/EtaThirdCusp
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/EtaThirdCusp
   mirror-E: none(waiver:initial-component-review)
   anchors: [mathlib/module/Mathlib.NumberTheory.ModularForms.Discriminant]
   utility: none
   digest: Exact principal-root phases at the third cusps for Kane's Euler quotient. -/

import D5.S3.Arith.ModularForms.EtaCuspTransform

/-! The ST cubed S eta multiplier and the exact reciprocal partition phase. -/

set_option autoImplicit false

noncomputable section

open Complex
open UpperHalfPlane hiding I
open scoped MatrixGroups ComplexConjugate

namespace D5.S3.Arith.ModularForms.EtaThirdCusp

open EtaCuspTransform

private lemma eta_add_three (τ : ℂ) :
    ModularForm.eta (τ + 3) = exp (Real.pi * I / 4) * ModularForm.eta τ := by
  have hq : exp (2 * Real.pi * I * (τ + 3)) = exp (2 * Real.pi * I * τ) := by
    have hperiod : exp (3 * (2 * Real.pi * I)) = 1 := by
      simpa using Complex.exp_int_mul_two_pi_mul_I (3 : ℤ)
    rw [show 2 * (Real.pi : ℂ) * I * (τ + 3) =
      2 * Real.pi * I * τ + 3 * (2 * Real.pi * I) by ring, exp_add,
      hperiod]
    simp
  have he : exp (2 * Real.pi * I * (τ + 3) / 24) =
      exp (Real.pi * I / 4) * exp (2 * Real.pi * I * τ / 24) := by
    rw [← exp_add]
    congr 1
    ring
  unfold ModularForm.eta
  simp only [ModularForm.eta_q, Function.Periodic.qParam, ofReal_ofNat,
    ofReal_one, div_one]
  rw [hq, he]
  ring

private lemma sqrt_I_exp : Complex.sqrt I = exp (Real.pi * I / 4) := by
  rw [sqrt_eq_exp I_ne_zero, Complex.log_I]
  congr 1
  ring

/-- The `ST³S` matrix is the cusp matrix for `(h,l,H)=(1,3,-1)`. Evaluating
its constant eta ratio at `I` fixes the principal branch on all of `ℍ`. -/
theorem eta_third_cusp : ∀ τ : ℍ,
    ModularForm.eta (cuspMatrix 3 1 (-1) 0 (by norm_num) • τ : ℍ) =
      exp (-Real.pi * I / 4) *
        Complex.sqrt (denom (cuspMatrix 3 1 (-1) 0 (by norm_num)) τ) * ModularForm.eta τ := by
  let γ := cuspMatrix 3 1 (-1) 0 (by norm_num)
  have hST : γ = ModularGroup.S * ModularGroup.T ^ 3 * ModularGroup.S := by decide
  obtain ⟨ξ, _, _, hξ⟩ := EtaCuspMultiplier.eta_unit_multiplier γ (by norm_num [γ, cuspMatrix])
  have hγI : ((γ • UpperHalfPlane.I : ℍ) : ℂ) = -1 / (3 + I) := by
    rw [hST, mul_smul, mul_smul]
    change ((ModularGroup.S • (ModularGroup.T ^ (3 : ℤ) •
      (ModularGroup.S • UpperHalfPlane.I)) : ℍ) : ℂ) = _
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_T_zpow_smul,
      UpperHalfPlane.modular_S_smul]
    simp [UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_I, add_comm]
    rw [show -I + (-3 : ℂ) = -(I + 3) by ring, inv_neg]
    simp [div_eq_mul_inv]
  have hden : denom γ UpperHalfPlane.I = I * (3 + I) := by
    change (((3 : ℤ) : ℝ) : ℂ) * I + (((-1 : ℤ) : ℝ) : ℂ) = _
    norm_num
    ring_nf
    simp [I_sq]
    <;> ring
  have hsI : Complex.sqrt I ≠ 0 := by simp [Complex.sqrt]
  have hsu : Complex.sqrt (3 + I) ≠ 0 := by
    change (3 + I) ^ (2⁻¹ : ℂ) ≠ 0
    apply Complex.cpow_ne_zero_iff.mpr
    left
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hη : ModularForm.eta I ≠ 0 := ModularForm.eta_ne_zero (by simp)
  have he : ModularForm.eta (γ • UpperHalfPlane.I : ℍ) =
      Complex.sqrt (3 + I) * ModularForm.eta I := by
    rw [hγI]
    have hS := ModularForm.eta_comp_eq_csqrt_I_inv (show 0 < (3 + I).im by norm_num)
    change ModularForm.eta (-1 / (3 + I)) =
      (Complex.sqrt I)⁻¹ * (Complex.sqrt (3 + I) * ModularForm.eta (3 + I)) at hS
    rw [hS, show (3 : ℂ) + I = I + 3 by ring, eta_add_three, ← sqrt_I_exp]
    field_simp
  have hr := hξ UpperHalfPlane.I
  rw [he, hden, sqrt_I_mul_of_re_pos (by norm_num : 0 < (3 + I).re)] at hr
  simp only [UpperHalfPlane.coe_I] at hr
  have hξI : ξ * Complex.sqrt I = 1 := by
    apply (mul_right_cancel₀ (mul_ne_zero hsu hη))
    convert hr.symm using 1 <;> ring
  have hphase : ξ = exp (-Real.pi * I / 4) := by
    have hi : ξ = (Complex.sqrt I)⁻¹ := by
      calc
        ξ = (ξ * Complex.sqrt I) * (Complex.sqrt I)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hsI, mul_one]
        _ = (Complex.sqrt I)⁻¹ := by rw [hξI, one_mul]
    rw [hi, sqrt_I_exp, ← exp_neg]
    congr 1
    ring
  intro τ
  simpa only [hphase] using hξ τ

/-- Exact reciprocal-partition phase at `1/3`, on the whole right half-plane. -/
theorem partition_one_third (w : ℂ) (hw : 0 < w.re) :
    partitionProduct (exp (2 * Real.pi * I / 3 - w)) =
      exp (Real.pi * I / 18) * Complex.sqrt (3 * w / (2 * Real.pi)) *
      exp (Real.pi ^ 2 / (54 * w) - w / 24) *
      partitionProduct (exp (-2 * Real.pi * I / 3 - 4 * Real.pi ^ 2 / (9 * w))) := by
  have he := eta_third_cusp (cuspPoint 3 1 w hw)
  rw [cusp_action 3 (by norm_num) 1 (-1) 0 (by norm_num) w hw,
    cusp_denom 3 (by norm_num) 1 (-1) 0 (by norm_num) w hw] at he
  have ht := partition_cusp_of_eta 3 (by norm_num) 1 (-1)
    (exp (-Real.pi * I / 4)) w hw (by
      have hp := (cuspMatrix 3 1 (-1) 0 (by norm_num) • cuspPoint 3 1 w hw : ℍ).im_pos
      change 0 < ((cuspMatrix 3 1 (-1) 0 (by norm_num) • cuspPoint 3 1 w hw : ℍ) : ℂ).im at hp
      rwa [show ((cuspMatrix 3 1 (-1) 0 (by norm_num) • cuspPoint 3 1 w hw : ℍ) : ℂ) =
        ((-1 : ℤ) : ℂ) / 3 + 2 * Real.pi * I / ((3 : ℂ) ^ 2 * w) from
        cusp_action 3 (by norm_num) 1 (-1) 0 (by norm_num) w hw] at hp) he
  have hp : exp (-Real.pi * I / 4) * Complex.sqrt I *
      exp (Real.pi * I * ((1 : ℂ) - (-1)) / (12 * 3)) = exp (Real.pi * I / 18) := by
    rw [sqrt_I_exp, ← exp_add, ← exp_add]
    congr 1
    ring
  norm_num at ht hp
  rw [hp] at ht
  convert ht using 1 <;> congr 2 <;> ring

end D5.S3.Arith.ModularForms.EtaThirdCusp

#print axioms D5.S3.Arith.ModularForms.EtaThirdCusp.eta_third_cusp
#print axioms D5.S3.Arith.ModularForms.EtaThirdCusp.partition_one_third
