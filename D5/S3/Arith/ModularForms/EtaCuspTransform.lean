/- GID: D5/S3/Arith/ModularForms/EtaCuspTransform
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/EtaCuspTransform
   mirror-E: none(waiver:initial-component-review)
   anchors: [mathlib/module/Mathlib.NumberTheory.ModularForms.DedekindEta]
   utility: none
   digest: The reciprocal Euler product at every coprime cusp with a constant unit phase. -/

import D5.S3.Arith.ModularForms.EtaCuspMultiplier

/-! Exact unshifted reciprocal Euler-product transformations on the whole open
right half-plane. Constants are obtained from the connected eta ratio. -/

set_option autoImplicit false

noncomputable section

open Complex
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace D5.S3.Arith.ModularForms.EtaCuspTransform

/-- Euler's product, without the eta exponential shift. -/
def eulerProduct (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1))

/-- The reciprocal partition product `P=1/E`, not Euler's product `E`. -/
def partitionProduct (q : ℂ) : ℂ := (eulerProduct q)⁻¹

/-- Principal-root multiplication by `I` throughout the open right half-plane. -/
theorem sqrt_I_mul_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.sqrt (I * z) = Complex.sqrt I * Complex.sqrt z := by
  have hz0 : z ≠ 0 := by intro h; simpa [h] using hz
  have ha := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  rw [sqrt_eq_exp (mul_ne_zero I_ne_zero hz0),
    Complex.log_mul I_ne_zero hz0 (by
      rw [Complex.arg_I]
      exact ⟨by linarith [Real.pi_pos], by linarith⟩),
    add_div, Complex.exp_add, ← sqrt_eq_exp I_ne_zero,
    ← sqrt_eq_exp hz0]

/-- The unshifted reciprocal product in eta coordinates. -/
theorem partitionProduct_qParam (τ : ℂ) :
    partitionProduct (exp (2 * Real.pi * I * τ)) =
      exp (Real.pi * I * τ / 12) / ModularForm.eta τ := by
  have he : ModularForm.eta τ =
      exp (Real.pi * I * τ / 12) * eulerProduct (exp (2 * Real.pi * I * τ)) := by
    unfold ModularForm.eta eulerProduct
    simp only [ModularForm.eta_q, Function.Periodic.qParam, ofReal_one, div_one,
      ofReal_ofNat]
    congr 1
    congr 1
    ring
  rw [he, partitionProduct]
  simp only [div_eq_mul_inv, mul_inv_rev]
  rw [mul_left_comm, mul_inv_cancel₀ (Complex.exp_ne_zero _), mul_one]

/-- The modular matrix with inverse cusp numerator `H`; the relation implies
coprimality and makes its determinant exactly one. -/
def cuspMatrix (l : ℕ) (h H b : ℤ) (hrel : h * H + 1 = (l : ℤ) * b) : SL(2, ℤ) :=
  ⟨!![H, -b; (l : ℤ), -h], by
    norm_num [Matrix.det_fin_two]
    nlinarith [hrel]⟩

/-- Cusp coordinate for every `Re(w)>0`; no restriction on its imaginary part. -/
def cuspPoint (l : ℕ) (h : ℤ) (w : ℂ) (hw : 0 < w.re) : ℍ :=
  ⟨(h : ℂ) / l + I * w / (2 * Real.pi), by
    have ht : ((h : ℂ) / l + I * w / (2 * Real.pi)).im = w.re / (2 * Real.pi) := by
      simp [Complex.div_im, Complex.mul_im]
      field_simp
    rw [ht]
    exact div_pos hw (mul_pos (by norm_num) Real.pi_pos)⟩

theorem cusp_denom (l : ℕ) (hl : 0 < l) (h H b : ℤ)
    (hrel : h * H + 1 = (l : ℤ) * b) (w : ℂ) (hw : 0 < w.re) :
    denom (cuspMatrix l h H b hrel) (cuspPoint l h w hw) =
      I * ((l : ℂ) * w / (2 * Real.pi)) := by
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hl)
  change (((l : ℤ) : ℝ) : ℂ) * ((h : ℂ) / l + I * w / (2 * Real.pi)) +
    (((-h : ℤ) : ℝ) : ℂ) = _
  push_cast
  field_simp
  ring

theorem cusp_action (l : ℕ) (hl : 0 < l) (h H b : ℤ)
    (hrel : h * H + 1 = (l : ℤ) * b) (w : ℂ) (hw : 0 < w.re) :
    ((cuspMatrix l h H b hrel • cuspPoint l h w hw : ℍ) : ℂ) =
      (H : ℂ) / l + 2 * Real.pi * I / ((l : ℂ) ^ 2 * w) := by
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hl)
  have hw0 : w ≠ 0 := by intro h; simpa [h] using hw
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hr : (h : ℂ) * (H : ℂ) + 1 = (l : ℂ) * b := by exact_mod_cast hrel
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [cuspMatrix, cuspPoint]
  change ((H : ℂ) * ((h : ℂ) / l + I * w / (2 * Real.pi)) - b) /
    ((l : ℂ) * ((h : ℂ) / l + I * w / (2 * Real.pi)) - h) = _
  have hd : (l : ℂ) * ((h : ℂ) / l + I * w / (2 * Real.pi)) - h =
      I * ((l : ℂ) * w / (2 * Real.pi)) := by
    field_simp
    ring
  rw [hd]
  field_simp
  ring_nf
  simp only [I_sq]
  linear_combination (2 * (Real.pi : ℂ)) * hr

/-- Algebraic eta-to-partition normalization at a cusp. This helper is consumed
by the general and exact phase transforms; the eta premise is proved there. -/
theorem partition_cusp_of_eta (l : ℕ) (hl : 0 < l) (h H : ℤ) (ξ : ℂ)
    (w : ℂ) (hw : 0 < w.re)
    (hupper : 0 < ((H : ℂ) / l + 2 * Real.pi * I / ((l : ℂ) ^ 2 * w)).im)
    (he : ModularForm.eta ((H : ℂ) / l + 2 * Real.pi * I / ((l : ℂ) ^ 2 * w)) =
      ξ * Complex.sqrt (I * ((l : ℂ) * w / (2 * Real.pi))) *
        ModularForm.eta ((h : ℂ) / l + I * w / (2 * Real.pi))) :
    partitionProduct (exp (2 * Real.pi * I * h / l - w)) =
      (ξ * Complex.sqrt I * exp (Real.pi * I * (h - H) / (12 * (l : ℂ)))) *
      Complex.sqrt ((l : ℂ) * w / (2 * Real.pi)) *
      exp (Real.pi ^ 2 / (6 * (l : ℂ) ^ 2 * w) - w / 24) *
      partitionProduct (exp (2 * Real.pi * I * H / l -
        4 * Real.pi ^ 2 / ((l : ℂ) ^ 2 * w))) := by
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hl)
  have hw0 : w ≠ 0 := by intro h; simpa [h] using hw
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  let τ := (h : ℂ) / l + I * w / (2 * Real.pi)
  let τ' := (H : ℂ) / l + 2 * Real.pi * I / ((l : ℂ) ^ 2 * w)
  have ht : 2 * Real.pi * I * τ = 2 * Real.pi * I * h / l - w := by
    dsimp [τ]
    field_simp
    ring_nf
    simp [I_sq]
    <;> ring
  have ht' : 2 * Real.pi * I * τ' = 2 * Real.pi * I * H / l -
      4 * Real.pi ^ 2 / ((l : ℂ) ^ 2 * w) := by
    dsimp [τ']
    field_simp
    ring_nf
    simp [I_sq]
    <;> ring
  have hroot : 0 < (((l : ℂ) * w / (2 * Real.pi)).re) := by
    simp [Complex.div_re, Complex.mul_re]
    positivity
  have hex : exp (Real.pi * I * (h - H) / (12 * (l : ℂ))) *
      exp (Real.pi ^ 2 / (6 * (l : ℂ) ^ 2 * w) - w / 24) *
      exp (Real.pi * I * τ' / 12) = exp (Real.pi * I * τ / 12) := by
    rw [← exp_add, ← exp_add]
    congr 1
    dsimp [τ, τ']
    field_simp
    ring_nf
    simp [I_sq]
    <;> ring
  rw [← ht, ← ht', partitionProduct_qParam, partitionProduct_qParam]
  rw [sqrt_I_mul_of_re_pos hroot] at he
  change ModularForm.eta τ' =
    ξ * (Complex.sqrt I * Complex.sqrt ((l : ℂ) * w / (2 * Real.pi))) *
      ModularForm.eta τ at he
  have hη := ModularForm.eta_ne_zero (cuspPoint l h w hw).im_pos
  have hη' : ModularForm.eta τ' ≠ 0 := ModularForm.eta_ne_zero hupper
  change ModularForm.eta τ ≠ 0 at hη
  rw [← mul_div_assoc]
  apply (div_eq_div_iff hη hη').mpr
  rw [he, ← hex]
  ring

/-- The first general cusp supplier: a single unit phase works for every
`Re(w)>0`. The inverse-numerator relation contains all original coprime data.
No transformation premise or extra branch restriction is assumed. -/
theorem partition_cusp_transform (l : ℕ) (hl : 0 < l) (h H : ℤ)
    (hcong : (l : ℤ) ∣ h * H + 1) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ w : ℂ, 0 < w.re →
      partitionProduct (exp (2 * Real.pi * I * h / l - w)) =
        ζ * Complex.sqrt ((l : ℂ) * w / (2 * Real.pi)) *
        exp (Real.pi ^ 2 / (6 * (l : ℂ) ^ 2 * w) - w / 24) *
        partitionProduct (exp (2 * Real.pi * I * H / l -
          4 * Real.pi ^ 2 / ((l : ℂ) ^ 2 * w))) := by
  obtain ⟨b, hb⟩ := hcong
  let γ := cuspMatrix l h H b hb
  have hc : 0 < γ 1 0 := by simpa [γ, cuspMatrix] using hl
  obtain ⟨ξ, hξpow, hξnorm, hξ⟩ := EtaCuspMultiplier.eta_unit_multiplier γ hc
  refine ⟨ξ * Complex.sqrt I * exp (Real.pi * I * (h - H) / (12 * (l : ℂ))), ?_, ?_⟩
  · have hs : ‖Complex.sqrt I‖ = 1 := by
      apply Complex.norm_eq_one_of_pow_eq_one (n := 8) _ (by norm_num)
      rw [show 8 = 2 * 4 by norm_num, pow_mul]
      simp [Complex.sqrt]
    simp [norm_mul, hξnorm, hs, norm_exp, Complex.div_re, Complex.mul_re]
  · intro w hw
    apply partition_cusp_of_eta l hl h H ξ w hw
    · have hp := (γ • cuspPoint l h w hw : ℍ).im_pos
      change 0 < ((γ • cuspPoint l h w hw : ℍ) : ℂ).im at hp
      rwa [show ((γ • cuspPoint l h w hw : ℍ) : ℂ) =
        (H : ℂ) / l + 2 * Real.pi * I / ((l : ℂ) ^ 2 * w) from
        cusp_action l hl h H b hb w hw] at hp
    have he := hξ (cuspPoint l h w hw)
    rw [cusp_action l hl h H b hb w hw, cusp_denom l hl h H b hb w hw] at he
    exact he

end D5.S3.Arith.ModularForms.EtaCuspTransform

#print axioms D5.S3.Arith.ModularForms.EtaCuspTransform.partition_cusp_transform
