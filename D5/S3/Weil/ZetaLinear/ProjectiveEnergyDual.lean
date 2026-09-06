/- GID: D5/S3/Weil/ZetaLinear/ProjectiveEnergyDual
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaLinear/ProjectiveEnergyDual
   mirror-E: none(waiver:actual-projective-energy-certificate)
   anchors: []
   digest: Derive the actual shifted projective energy and certify directional readouts using full trial residuals. -/

import D5.S3.Weil.ZetaLinear.CoerciveDualCertificate
import D5.S3.Observer.Hankel.ProjectiveRayleighReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaLinear.ProjectiveEnergyDual

open D5.S3.Weil.ZetaLinear.CoerciveDualCertificate
open D5.S3.Observer.Hankel.ProjectiveRayleighReadout
open scoped ComplexInnerProductSpace

variable {H D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [AddCommGroup D] [Module ℂ D]

/-- A real shift of the actual domain operator, without changing its domain. -/
def shiftedAction (ι A : D →ₗ[ℂ] H) (ell : ℝ) : D →ₗ[ℂ] H := A - (ell : ℂ) • ι

private theorem shifted_energy (ι A : D →ₗ[ℂ] H) (ell : ℝ) (f : D) :
    domainEnergy ι (shiftedAction ι A ell) f =
      (⟪ι f, A f⟫_ℂ).re - ell * ‖ι f‖ ^ 2 := by
  simp [domainEnergy, shiftedAction, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, Complex.mul_re]

private theorem shifted_symmetry (ι A : D →ₗ[ℂ] H) (ell : ℝ)
    (hsym : ∀ x y : D, ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ) :
    ∀ x y : D, ⟪ι x, shiftedAction ι A ell y⟫_ℂ =
      ⟪shiftedAction ι A ell x, ι y⟫_ℂ := by
  intro x y
  simp [shiftedAction, inner_sub_right, inner_sub_left, inner_smul_right,
    inner_smul_left, hsym x y]

/-- The actual projective error has shifted energy at most U-ell, a stronger
input for directional readouts than an unweighted norm bound alone. Both
orthogonality and this energy bound are derived from the actual eigenvector. -/
theorem rayleigh_shifted_energy_bound (ι A : D →ₗ[ℂ] H) (k u : D)
    (ell U T lam : ℝ)
    (hsym : ∀ x y : D, ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ)
    (hk : ‖ι k‖ = 1) (hu : ι u ≠ 0) (hAu : A u = (lam : ℂ) • ι u)
    (hell : ell ≤ lam) (hlam : lam < T)
    (hU : (⟪ι k, A k⟫_ℂ).re ≤ U) (hT : U < T)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      T * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re) :
    let alpha := ⟪ι k, ι u⟫_ℂ
    let w := alpha⁻¹ • u - k
    alpha ≠ 0 ∧ ⟪ι k, ι w⟫_ℂ = 0 ∧
      0 ≤ domainEnergy ι (shiftedAction ι A ell) w ∧
      domainEnergy ι (shiftedAction ι A ell) w ≤ U - ell := by
  obtain ⟨ha, ho, he, _, hlt⟩ := rayleigh_projective_enclosure ι A k u
    ell U T lam hsym hk hu hAu hell hlam hU hT hcoercive
  let w := (⟪ι k, ι u⟫_ℂ)⁻¹ • u - k
  have hnorm : ‖ι w‖ ^ 2 < 1 := he.trans_lt hlt
  have hid := (projective_error_energy_identity ι A k u lam hsym hk hAu ha).2
  have hgap := hcoercive w ho
  have hpositive : 0 ≤ (T - ell) * ‖ι w‖ ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hpaid : 0 ≤ (lam - ell) * (1 - ‖ι w‖ ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hell) (by linarith)
  refine ⟨ha, ho, ?_, ?_⟩
  · rw [shifted_energy]
    nlinarith [hgap, hpositive]
  · rw [shifted_energy]
    change (⟪ι w, A w⟫_ℂ).re = _ at hid
    nlinarith [hid, hpaid, hU]

/-- Any actual orthogonal dual trial certifies a directional projective
readout. There is no assumed inverse, sensitivity, readout bound or error
identity. The residual uses the entire shifted action on the trial. -/
theorem rayleigh_dual_readout (ι A : D →ₗ[ℂ] H) (k u : D)
    (ell U T lam : ℝ)
    (hsym : ∀ x y : D, ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ)
    (hk : ‖ι k‖ = 1) (hu : ι u ≠ 0) (hAu : A u = (lam : ℂ) • ι u)
    (hell : ell ≤ lam) (hlam : lam < T)
    (hU : (⟪ι k, A k⟫_ℂ).re ≤ U) (hT : U < T)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      T * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re)
    (g : H) (v : D) (hv : ⟪ι k, ι v⟫_ℂ = 0) :
    let C := dualBudget ι (shiftedAction ι A ell) k g (T - ell) v
    ⟪ι k, ι u⟫_ℂ ≠ 0 ∧ 0 ≤ C ∧
      ‖⟪g, (⟪ι k, ι u⟫_ℂ)⁻¹ • ι u⟫_ℂ - ⟪g, ι k⟫_ℂ‖ ^ 2 ≤ C * (U - ell) := by
  obtain ⟨ha, ho, _, henergy⟩ := rayleigh_shifted_energy_bound ι A k u
    ell U T lam hsym hk hu hAu hell hlam hU hT hcoercive
  have hκ : 0 < T - ell := by linarith
  have hshift : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      (T - ell) * ‖ι f‖ ^ 2 ≤ domainEnergy ι (shiftedAction ι A ell) f := by
    intro f hf
    rw [shifted_energy]
    have h := hcoercive f hf
    nlinarith
  obtain ⟨hC, hbound⟩ := dual_energy_readout ι (shiftedAction ι A ell) k g
    (T - ell) hκ (shifted_symmetry ι A ell hsym) hshift v hv
  have h := (hbound ((⟪ι k, ι u⟫_ℂ)⁻¹ • u - k) ho).trans
    (mul_le_mul_of_nonneg_left henergy hC)
  refine ⟨ha, hC, ?_⟩
  simpa only [map_sub, map_smul, inner_sub_right] using h

#print axioms rayleigh_shifted_energy_bound
#print axioms rayleigh_dual_readout

end D5.S3.Weil.ZetaLinear.ProjectiveEnergyDual
