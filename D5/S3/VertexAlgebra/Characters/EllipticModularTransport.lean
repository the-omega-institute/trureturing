/- GID: D5/S3/VertexAlgebra/Characters/EllipticModularTransport
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Characters/EllipticModularTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral modular transport of period lattices and the continued annular current kernel. -/

import D5.S3.VertexAlgebra.Characters.AnnularCurrentKernel
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable section
open Complex
open scoped Real MatrixGroups

namespace D5.S3.VertexAlgebra.EllipticModularTransport
open AnnularCurrentKernel

private lemma det_one (γ : SL(2, ℤ)) :
    γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  simpa [Matrix.det_fin_two] using γ.det_coe

private def coordinates (γ : SL(2, ℤ)) : (ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ) where
  toFun p := (γ 0 0 * p.1 - γ 0 1 * p.2, -γ 1 0 * p.1 + γ 1 1 * p.2)
  invFun p := (γ 1 1 * p.1 + γ 0 1 * p.2, γ 1 0 * p.1 + γ 0 0 * p.2)
  left_inv p := by
    have h := det_one γ
    ext
    · dsimp; linear_combination h * p.1
    · dsimp; linear_combination h * p.2
  right_inv p := by
    have h := det_one γ
    ext
    · dsimp; linear_combination h * p.1
    · dsimp; linear_combination h * p.2
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' k p := by ext <;> simp [smul_eq_mul] <;> ring

/-- The integral change of basis inducing division by the modular denominator. -/
def modularLatticeEquiv (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    (periodPair τ).lattice ≃ₗ[ℤ] (periodPair (γ • τ)).lattice :=
  (periodPair τ).latticeEquivProd.trans
    ((coordinates γ).trans (periodPair (γ • τ)).latticeEquivProd.symm)

private lemma coe_modularLatticeEquiv (γ : SL(2, ℤ)) (τ : UpperHalfPlane)
    (l : (periodPair τ).lattice) :
    (modularLatticeEquiv γ τ l : ℂ) = (l : ℂ) / UpperHalfPlane.denom γ τ := by
  let p := (periodPair τ).latticeEquivProd l
  have hp : (l : ℂ) = (p.1 : ℂ) + p.2 * (τ : ℂ) := by
    simpa [p, periodPair] using
      (PeriodPair.latticeEquiv_symm_apply (periodPair τ) p)
  change ((periodPair (γ • τ)).latticeEquivProd.symm (coordinates γ p) : ℂ) = _
  rw [PeriodPair.latticeEquiv_symm_apply, hp]
  simp only [coordinates, periodPair, mul_one, Int.cast_sub, Int.cast_mul, Int.cast_neg,
    Int.cast_add]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  push_cast
  rw [ModularGroup.denom_apply]
  have hd : (γ 0 0 : ℂ) * γ 1 1 - (γ 0 1 : ℂ) * γ 1 0 = 1 := by
    exact_mod_cast det_one γ
  have hj := UpperHalfPlane.denom_ne_zero (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) τ
  rw [ModularGroup.denom_apply] at hj
  field_simp
  linear_combination hd * ((p.1 : ℂ) + p.2 * (τ : ℂ))

private lemma coe_modularLatticeEquiv_symm (γ : SL(2, ℤ)) (τ : UpperHalfPlane)
    (l : (periodPair (γ • τ)).lattice) :
    ((modularLatticeEquiv γ τ).symm l : ℂ) = UpperHalfPlane.denom γ τ * (l : ℂ) := by
  have h := coe_modularLatticeEquiv γ τ ((modularLatticeEquiv γ τ).symm l)
  simp only [LinearEquiv.apply_symm_apply] at h
  exact (eq_div_iff (UpperHalfPlane.denom_ne_zero _ τ)).mp h |>.symm.trans (mul_comm _ _)

private lemma div_denom_mem_lattice_iff (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (w : ℂ) :
    w / UpperHalfPlane.denom γ τ ∈ (periodPair (γ • τ)).lattice ↔
      w ∈ (periodPair τ).lattice := by
  constructor
  · intro h
    have he := coe_modularLatticeEquiv_symm γ τ ⟨_, h⟩
    simp only [mul_div_cancel₀, mul_div_cancel_left₀,
      UpperHalfPlane.denom_ne_zero] at he
    exact he ▸ ((modularLatticeEquiv γ τ).symm ⟨_, h⟩).property
  · intro h
    exact coe_modularLatticeEquiv γ τ ⟨w, h⟩ ▸ (modularLatticeEquiv γ τ ⟨w, h⟩).property

private lemma regularized_scale (w l j : ℂ) (hj : j ≠ 0) (hw : w / j - l / j ≠ 0) :
    1 / (w / j - l / j) ^ 2 - 1 / (l / j) ^ 2 =
      j ^ 2 * (1 / (w - l) ^ 2 - 1 / l ^ 2) := by
  have hwl : w - l ≠ 0 := by
    intro h
    apply hw
    rw [← sub_div, h, zero_div]
  rw [← sub_div, div_pow, div_pow]
  by_cases hl : l = 0
  · subst l
    simp only [zero_pow (by decide : 2 ≠ 0), zero_div, div_zero, sub_zero] at *
    field_simp
  · field_simp
    <;> ring

/-- Covariance of the original regularized lattice-defined Weierstrass function off its poles. -/
theorem weierstrassP_modular (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (w : ℂ)
    (hw : w ∉ (periodPair τ).lattice) :
    (periodPair (γ • τ)).weierstrassP (w / UpperHalfPlane.denom γ τ) =
      UpperHalfPlane.denom γ τ ^ 2 * (periodPair τ).weierstrassP w := by
  have hdomain := (div_denom_mem_lattice_iff γ τ w).not.mpr hw
  unfold PeriodPair.weierstrassP
  rw [← (modularLatticeEquiv γ τ).toEquiv.tsum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro l
  rw [coe_modularLatticeEquiv]
  apply regularized_scale _ _ _ (UpperHalfPlane.denom_ne_zero _ τ)
  have hne : w / UpperHalfPlane.denom γ τ - (modularLatticeEquiv γ τ l : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (fun h => hdomain (h.symm ▸ (modularLatticeEquiv γ τ l).property))
  simpa only [coe_modularLatticeEquiv] using hne

/-- The meromorphic continuation of the ordinary strict-annular scalar kernel. -/
def continuedKernel (τ : UpperHalfPlane) (w : ℂ) : ℂ :=
  (periodPair τ).weierstrassP w / (2 * π * I) ^ 2 - EisensteinSeries.E2 τ / 12

private lemma E2_transform (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    EisensteinSeries.E2 (γ • τ) = UpperHalfPlane.denom γ τ ^ 2 * EisensteinSeries.E2 τ +
      6 / (π * I) * (γ 1 0 : ℂ) * UpperHalfPlane.denom γ τ := by
  have h := congrArg (fun f : UpperHalfPlane → ℂ => f τ)
    (EisensteinSeries.E2_slash_action γ)
  simp only [ModularForm.SL_slash_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    EisensteinSeries.D2, zpow_neg, zpow_ofNat] at h
  rw [riemannZeta_two] at h
  have hj := UpperHalfPlane.denom_ne_zero (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) τ
  have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  calc
    EisensteinSeries.E2 (γ • τ) =
        (EisensteinSeries.E2 (γ • τ) * (UpperHalfPlane.denom γ τ ^ 2)⁻¹) *
          UpperHalfPlane.denom γ τ ^ 2 := by simp [mul_assoc, hj]
    _ = _ := by
      rw [h]
      field_simp
      simp only [I_sq]
      ring

/-- Full modular covariance with the normalized, generic lower-left-entry correction. -/
theorem continuedKernel_modular (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (w : ℂ)
    (hw : w ∉ (periodPair τ).lattice) :
    continuedKernel (γ • τ) (w / UpperHalfPlane.denom γ τ) =
      UpperHalfPlane.denom γ τ ^ 2 * continuedKernel τ w -
        (γ 1 0 : ℂ) * UpperHalfPlane.denom γ τ / (2 * π * I) := by
  unfold continuedKernel
  rw [weierstrassP_modular γ τ w hw, E2_transform]
  ring

private lemma strict_strip_not_mem (τ : UpperHalfPlane) (w : ℂ)
    (hw : 0 < w.im) (hwτ : w.im < τ.im) : w ∉ (periodPair τ).lattice := by
  intro h
  obtain ⟨m, n, h⟩ := PeriodPair.mem_lattice.mp h
  have hi := congrArg Complex.im h
  simp [periodPair] at hi
  have hn0 : (0 : ℝ) < n := by nlinarith [τ.im_pos]
  have hn1 : (n : ℝ) < 1 := by nlinarith [τ.im_pos]
  have : (0 : ℤ) < n := by exact_mod_cast hn0
  have : n < (1 : ℤ) := by exact_mod_cast hn1
  omega

/-- The original annular series transforms when both strict-strip conditions hold. -/
theorem annularKernel_modular_of_strictStrips
    (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (w : ℂ)
    (hw : 0 < w.im) (hwτ : w.im < τ.im)
    (hw' : 0 < (w / UpperHalfPlane.denom γ τ).im)
    (hwτ' : (w / UpperHalfPlane.denom γ τ).im < (γ • τ).im) :
    annularKernel (expCoord (γ • τ)) (expCoord (w / UpperHalfPlane.denom γ τ)) =
      UpperHalfPlane.denom γ τ ^ 2 * annularKernel (expCoord τ) (expCoord w) -
        (γ 1 0 : ℂ) * UpperHalfPlane.denom γ τ / (2 * π * I) := by
  rw [annular_kernel_eq_periodPair_weierstrassP_sub_E2 _ _ hw' hwτ',
    annular_kernel_eq_periodPair_weierstrassP_sub_E2 _ _ hw hwτ]
  exact continuedKernel_modular γ τ w (strict_strip_not_mem τ w hw hwτ)

end D5.S3.VertexAlgebra.EllipticModularTransport
