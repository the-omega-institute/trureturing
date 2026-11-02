/- GID: D5/S3/Arith/ModularForms/EtaCuspMultiplier
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/EtaCuspMultiplier
   mirror-E: none(waiver:initial-component-review)
   anchors: [mathlib/module/Mathlib.NumberTheory.ModularForms.Discriminant]
   utility: none
   digest: A constant unit eta multiplier for every positive lower-left modular entry. -/

import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! The discriminant determines an eta multiplier up to a constant 24th root of
unity. Continuity and connectedness make this a single constant on the entire
upper half-plane. This does not identify that constant with a Dedekind sum. -/

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane
open scoped MatrixGroups

namespace D5.S3.Arith.ModularForms.EtaCuspMultiplier

private def ratio (γ : SL(2, ℤ)) (τ : ℍ) : ℂ :=
  ModularForm.eta (γ • τ : ℍ) /
    (Complex.sqrt (denom γ τ) * ModularForm.eta τ)

private lemma denom_im_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (τ : ℍ) :
    0 < (denom γ τ).im := by
  have hc' : 0 < (γ 1 0 : ℝ) := by exact_mod_cast hc
  simpa [denom] using mul_pos hc' τ.im_pos

private lemma sqrt_denom_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    Complex.sqrt (denom γ τ) ≠ 0 := by
  simpa [Complex.sqrt] using
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (denom_ne_zero γ τ)))

private lemma ratio_pow (γ : SL(2, ℤ)) (τ : ℍ) : ratio γ τ ^ 24 = 1 := by
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant
    (γ := (γ : GL (Fin 2) ℝ)) (by exact ⟨γ, rfl⟩) τ
  change ModularForm.eta (γ • τ : ℍ) ^ 24 =
    denom γ τ ^ (12 : ℤ) * ModularForm.eta τ ^ 24 at hΔ
  rw [zpow_ofNat] at hΔ
  have hs : Complex.sqrt (denom γ τ) ^ 24 = denom γ τ ^ 12 := by
    rw [show 24 = 2 * 12 by norm_num, pow_mul]
    simp [Complex.sqrt]
  rw [ratio, div_pow, mul_pow, hs, hΔ]
  exact div_self (mul_ne_zero (pow_ne_zero _ (denom_ne_zero γ τ))
    (pow_ne_zero _ (ModularForm.eta_ne_zero τ.im_pos)))

private lemma continuous_eta : Continuous (fun τ : ℍ => ModularForm.eta τ) := by
  refine continuous_iff_continuousAt.mpr fun τ => ?_
  exact (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet τ.im_pos).continuousAt.comp
    UpperHalfPlane.continuous_coe.continuousAt

private lemma continuous_ratio (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    Continuous (ratio γ) := by
  have hden : Continuous (fun τ : ℍ => denom γ τ) := by
    unfold denom
    fun_prop
  have hs : Continuous (fun τ : ℍ => Complex.sqrt (denom γ τ)) := by
    refine continuous_iff_continuousAt.mpr fun τ => ?_
    exact (Complex.continuousAt_sqrt (Or.inr (ne_of_gt (denom_im_pos γ hc τ)))).comp
      (f := fun t : ℍ => denom γ t) hden.continuousAt
  have hact : Continuous (fun τ : ℍ => γ • τ) := by
    change Continuous (fun τ : ℍ => (γ : GL (Fin 2) ℝ) • τ)
    exact continuous_const_smul _
  unfold ratio
  exact (continuous_eta.comp hact).div (hs.mul continuous_eta)
    (fun τ => mul_ne_zero (sqrt_denom_ne_zero γ τ) (ModularForm.eta_ne_zero τ.im_pos))

/-- Every integral modular matrix with positive lower-left entry has one eta
multiplier, independent of the upper-half-plane variable. The square root is
principal. Its 24th power, rather than any asserted Dedekind-sum formula, is one. -/
theorem eta_unit_multiplier (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    ∃ ξ : ℂ, ξ ^ 24 = 1 ∧ ‖ξ‖ = 1 ∧
      ∀ τ : ℍ, ModularForm.eta (γ • τ : ℍ) =
        ξ * Complex.sqrt (denom γ τ) * ModularForm.eta τ := by
  have hf : Set.Finite {z : ℂ | z ^ 24 = 1} := by
    simpa [Polynomial.IsRoot, sub_eq_zero] using
      (Polynomial.finite_setOfPred_isRoot
        (Polynomial.X_pow_sub_C_ne_zero (by norm_num : 0 < 24) (1 : ℂ)))
  have heq (τ : ℍ) : ratio γ τ = ratio γ UpperHalfPlane.I := by
    exact isPreconnected_univ.constant_of_mapsTo hf.isDiscrete
      (continuous_ratio γ hc).continuousOn (fun z _ => ratio_pow γ z)
      (Set.mem_univ τ) (Set.mem_univ UpperHalfPlane.I)
  refine ⟨ratio γ UpperHalfPlane.I, ratio_pow γ UpperHalfPlane.I,
    Complex.norm_eq_one_of_pow_eq_one (ratio_pow γ UpperHalfPlane.I) (by norm_num), ?_⟩
  intro τ
  have hne := mul_ne_zero (sqrt_denom_ne_zero γ τ) (ModularForm.eta_ne_zero τ.im_pos)
  have h := (div_eq_iff hne).mp (heq τ)
  simpa only [mul_assoc] using h

end D5.S3.Arith.ModularForms.EtaCuspMultiplier

#print axioms D5.S3.Arith.ModularForms.EtaCuspMultiplier.eta_unit_multiplier
