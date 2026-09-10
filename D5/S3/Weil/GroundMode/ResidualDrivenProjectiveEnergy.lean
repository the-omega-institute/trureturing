/- GID: D5/S3/Weil/GroundMode/ResidualDrivenProjectiveEnergy
   generality: G
   mirror-B: D5/B/S3/Weil/GroundMode/ResidualDrivenProjectiveEnergy
   mirror-E: none(waiver:actual-inverse-energy-Schur-and-sector-domain-certificate)
   anchors: []
   utility: none
   digest: Bound the actual projective eigenvector energy from the candidate residual's complete dual energy, without an absolute lower eigenvalue premise. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Residual-driven projective energy

The concrete Weil consumer takes M=A-U on the invariant even operator domain.
Its ground eigenvalue after this shift is nonpositive. Complete inverse-energy
Schur estimates certify the functional of the *actual candidate residual* on
k's complement. The eigen-equation then controls projective error energy
without supplying an absolute uniform lower bound on the ground eigenvalue.

The residual functional bound is independently computed, not an assumption
on the desired ground error. The theorem also proves the nonzero overlap and
orthogonality required for projective normalization. It needs only linearity,
the eigen-equation and real-part complement coercivity; the self-adjoint
spectral realization belongs to the concrete consumer's separate hypotheses.

The numerical consumer preserves all high modes, uses the actual same-scale
candidate and true prolate family, and identifies the relevant even sector.
The inverse-form Schur identity, Fourier/core correspondence and interval
arithmetic engine remain paper/computer-assisted bridges. No all-scale rate,
Xi limit, compiled Lean verdict or new classical-method priority is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.GroundMode.ResidualDrivenProjectiveEnergy

open scoped InnerProductSpace

variable {H D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [AddCommGroup D] [Module ℂ D]

/-- A complete dual-energy estimate for the actual candidate residual bounds
projective eigenvector energy. In the Weil application the domain is the even
invariant domain, M=A-U, and lam=lambda_0-U<=0. No lower bound on lambda_0,
small unweighted residual, or proposed projective error bound is an input. -/
theorem residual_driven_projective_energy
    (ι M : D →ₗ[ℂ] H) (k u : D) (lam kap E : ℝ)
    (hk : ‖ι k‖ = 1) (hu : ι u ≠ 0)
    (hMu : M u = (lam : ℂ) • ι u) (hlam : lam ≤ 0)
    (hkap : 0 < kap) (hE : 0 ≤ E)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      kap * ‖ι f‖ ^ 2 ≤ (⟪ι f, M f⟫_ℂ).re)
    (hresidual : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      ‖⟪ι f, M k - ((⟪ι k, M k⟫_ℂ).re : ℂ) • ι k⟫_ℂ‖ ^ 2 ≤
        E * (⟪ι f, M f⟫_ℂ).re) :
    let alpha := ⟪ι k, ι u⟫_ℂ
    let w := alpha⁻¹ • u - k
    alpha ≠ 0 ∧ ⟪ι k, ι w⟫_ℂ = 0 ∧
      0 ≤ (⟪ι w, M w⟫_ℂ).re ∧
      (⟪ι w, M w⟫_ℂ).re ≤ E ∧ ‖ι w‖ ^ 2 ≤ E / kap := by
  have heigen : (⟪ι u, M u⟫_ℂ).re = lam * ‖ι u‖ ^ 2 := by
    rw [hMu, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow, Complex.mul_re]
  have hn : 0 < ‖ι u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have ha : ⟪ι k, ι u⟫_ℂ ≠ 0 := by
    intro hz
    have hg := hcoercive u hz
    rw [heigen] at hg
    have hneg := mul_nonpos_of_nonpos_of_nonneg hlam hn.le
    have hpos := mul_pos hkap hn
    linarith
  let alpha := ⟪ι k, ι u⟫_ℂ
  let w := alpha⁻¹ • u - k
  change alpha ≠ 0 ∧ ⟪ι k, ι w⟫_ℂ = 0 ∧ _
  have ho : ⟪ι k, ι w⟫_ℂ = 0 := by
    dsimp [w, alpha]
    simp [map_sub, map_smul, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hk, ha]
  have hok : ⟪ι w, ι k⟫_ℂ = 0 := inner_eq_zero_symm.mp ho
  have haction : M w = (lam : ℂ) • ι w - (M k - (lam : ℂ) • ι k) := by
    dsimp [w]
    simp only [map_sub, map_smul, hMu]
    module
  have hidentity : (⟪ι w, M w⟫_ℂ).re =
      lam * ‖ι w‖ ^ 2 - (⟪ι w, M k⟫_ℂ).re := by
    rw [haction, inner_sub_right, inner_sub_right, inner_smul_right,
      inner_smul_right, hok, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow, Complex.mul_re]
  have hpair :
      ⟪ι w, M k - ((⟪ι k, M k⟫_ℂ).re : ℂ) • ι k⟫_ℂ = ⟪ι w, M k⟫_ℂ := by
    rw [inner_sub_right, inner_smul_right, hok, mul_zero, sub_zero]
  have hr := hresidual w ho
  rw [hpair] at hr
  have hg := hcoercive w ho
  have hq : 0 ≤ (⟪ι w, M w⟫_ℂ).re :=
    (mul_nonneg hkap.le (sq_nonneg _)).trans hg
  have hlinear : (⟪ι w, M w⟫_ℂ).re ≤ ‖⟪ι w, M k⟫_ℂ‖ := by
    have hneg := mul_nonpos_of_nonpos_of_nonneg hlam (sq_nonneg ‖ι w‖)
    have habs := (neg_le_abs (⟪ι w, M k⟫_ℂ).re).trans
      (Complex.abs_re_le_norm ⟪ι w, M k⟫_ℂ)
    linarith [hidentity]
  have hsquare := (sq_le_sq₀ hq (norm_nonneg _)).mpr hlinear
  have hbound : (⟪ι w, M w⟫_ℂ).re ≤ E := by
    by_contra h
    have hlt : E < (⟪ι w, M w⟫_ℂ).re := lt_of_not_ge h
    have hp := mul_pos (lt_of_le_of_lt hE hlt) (sub_pos.mpr hlt)
    nlinarith
  refine ⟨ha, ho, hq, hbound, ?_⟩
  apply (le_div_iff₀ hkap).mpr
  simpa only [mul_comm] using hg.trans hbound

#print axioms residual_driven_projective_energy

end D5.S3.Weil.GroundMode.ResidualDrivenProjectiveEnergy
