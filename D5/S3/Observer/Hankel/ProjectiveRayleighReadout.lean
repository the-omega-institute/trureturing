/- GID: D5/S3/Observer/Hankel/ProjectiveRayleighReadout
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/ProjectiveRayleighReadout
   mirror-E: none(waiver:unbounded-domain-analytic-theorem)
   anchors: []
   digest: Complex projective recovery from Rayleigh enclosures and sharp scalar-readout certification. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The motivating open problem is the actual ground-mode approximation in
Connes--Consani--Moscovici, arXiv:2511.22755v1, Section 8.  This file proves
an analytic bridge, not that open problem.  The data are a genuine linear
operator domain, a unit candidate, an actual eigenvector, an eigenvalue
lower enclosure, and a codimension-one form lower bound.

The real predecessor is WeilRayleighEnclosureModeCapture on PR #5602.
Here the field is complex; the eigenvector need not be normalized; its
overlap is proved nonzero; no eigenvalue <= candidate-energy hypothesis
is needed.  The final constant is (upper-lower)/(threshold-lower).

The scalar-readout bound uses the orthogonal part of the actual readout
vector.  The exact converse is proved in ProjectiveReadoutSharpness.
No equality of full determinants follows from these statements.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Hankel.ProjectiveRayleighReadout

open scoped ComplexInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem real_eigen_energy (x : H) (lam : ℝ) :
    (⟪x, (lam : ℂ) • x⟫_ℂ).re = lam * ‖x‖ ^ 2 := by
  simp [inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.mul_re]

/-- A nonzero eigenvector below the candidate-orthogonal threshold cannot
be orthogonal to the candidate.  Only a linear operator domain is used. -/
theorem rayleigh_overlap_ne_zero
    {D : Type*} [AddCommGroup D] [Module ℂ D]
    (ι A : D →ₗ[ℂ] H) (k u : D) (lam threshold : ℝ)
    (hu : ι u ≠ 0) (hAu : A u = (lam : ℂ) • ι u)
    (hlam : lam < threshold)
    (hgap : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      threshold * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re) :
    ⟪ι k, ι u⟫_ℂ ≠ 0 := by
  intro hzero
  have h := hgap u hzero
  rw [hAu, real_eigen_energy] at h
  have hn : 0 < ‖ι u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hcontra := (mul_le_mul_iff_right₀ hn).mp h
  exact (not_le_of_gt hlam) hcontra

/-- Normalize by the proved nonzero candidate overlap.  The error is exactly
orthogonal to the candidate, and its energy identity is derived from the
actual domain action and symmetry. -/
theorem projective_error_energy_identity
    {D : Type*} [AddCommGroup D] [Module ℂ D]
    (ι A : D →ₗ[ℂ] H) (k u : D) (lam : ℝ)
    (hsym : ∀ x y : D, ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ)
    (hk : ‖ι k‖ = 1) (hAu : A u = (lam : ℂ) • ι u)
    (halpha : ⟪ι k, ι u⟫_ℂ ≠ 0) :
    let w := (⟪ι k, ι u⟫_ℂ)⁻¹ • u - k
    ⟪ι k, ι w⟫_ℂ = 0 ∧
      (⟪ι w, A w⟫_ℂ).re = lam * ‖ι w‖ ^ 2 + (⟪ι k, A k⟫_ℂ).re - lam := by
  let alpha := ⟪ι k, ι u⟫_ℂ
  let z := alpha⁻¹ • u
  let w := z - k
  have hzinner : ⟪ι k, ι z⟫_ℂ = 1 := by
    simp [z, alpha, inner_smul_right, halpha]
  have horth : ⟪ι k, ι w⟫_ℂ = 0 := by
    simp only [w, map_sub, inner_sub_right, hzinner,
      inner_self_eq_norm_sq_to_K, hk, Complex.ofReal_one, one_pow, sub_self]
  have horth' : ⟪ι w, ι k⟫_ℂ = 0 := inner_eq_zero_symm.mp horth
  have hz : z = k + w := by
    dsimp only [w]
    abel
  have hAz : A z = (lam : ℂ) • ι z := by
    simp only [z, map_smul, hAu, smul_smul]
    rw [mul_comm]
  have hcross : (⟪ι w, A k⟫_ℂ).re = (⟪ι k, A w⟫_ℂ).re := by
    rw [hsym w k]
    exact inner_re_symm (𝕜 := ℂ) (A w) (ι k)
  have hkz : (⟪ι k, A k⟫_ℂ).re + (⟪ι k, A w⟫_ℂ).re = lam := by
    have h := congrArg (fun y : H => (⟪ι k, y⟫_ℂ).re) hAz
    have hleft : (⟪ι k, A z⟫_ℂ).re =
        (⟪ι k, A k⟫_ℂ).re + (⟪ι k, A w⟫_ℂ).re := by
      rw [hz, map_add, inner_add_right, Complex.add_re]
    rw [hleft, inner_smul_right, hzinner, mul_one, Complex.ofReal_re] at h
    exact h
  have hwz : (⟪ι w, A k⟫_ℂ).re + (⟪ι w, A w⟫_ℂ).re =
      lam * ‖ι w‖ ^ 2 := by
    have h := congrArg (fun y : H => (⟪ι w, y⟫_ℂ).re) hAz
    rw [hz, map_add, map_add, inner_add_right, inner_smul_right,
      inner_add_right, horth', zero_add, inner_self_eq_norm_sq_to_K] at h
    simpa [Complex.mul_re] using h
  exact ⟨horth, by linarith [hcross, hkz, hwz]⟩

/-- Scalar enclosure transfer used by the projective theorem.  Its proof also
shows that the error is below one, avoiding a spurious extra width condition. -/
theorem projective_budget_transfer
    (lower upper threshold lam mu err : ℝ)
    (herr : 0 ≤ err) (hlower : lower ≤ lam) (hlam : lam < threshold)
    (hupper : mu ≤ upper) (hgap : upper < threshold)
    (henergy : (threshold - lam) * err ≤ mu - lam) :
    err ≤ (upper - lower) / (threshold - lower) ∧
      0 ≤ (upper - lower) / (threshold - lower) ∧
      (upper - lower) / (threshold - lower) < 1 := by
  have hden : 0 < threshold - lower := by linarith
  have hgaplam : 0 < threshold - lam := sub_pos.mpr hlam
  have herrlt : err < 1 := by
    apply (mul_lt_mul_iff_left₀ hgaplam).mp
    calc
      (threshold - lam) * err ≤ mu - lam := henergy
      _ < threshold - lam := by linarith
      _ = (threshold - lam) * 1 := by ring
  have hext := mul_le_mul_of_nonneg_left (le_of_lt herrlt) (sub_nonneg.mpr hlower)
  have hbound : (threshold - lower) * err ≤ upper - lower := by nlinarith
  have hratio : err ≤ (upper - lower) / (threshold - lower) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [hbound]
  exact ⟨hratio, herr.trans hratio, (div_lt_one hden).mpr (by linarith)⟩

/-- Full complex, projectively normalized enclosure theorem for a possibly
unbounded symmetric operator.  Nonzero overlap, candidate-orthogonality and
the improved error budget are conclusions.  Neither eigenvector unit norm
nor a supplied residual identity is a premise. -/
theorem rayleigh_projective_enclosure
    {D : Type*} [AddCommGroup D] [Module ℂ D]
    (ι A : D →ₗ[ℂ] H) (k u : D) (lower upper threshold lam : ℝ)
    (hsym : ∀ x y : D, ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ)
    (hk : ‖ι k‖ = 1) (hu : ι u ≠ 0)
    (hAu : A u = (lam : ℂ) • ι u)
    (hlower : lower ≤ lam) (hlam : lam < threshold)
    (hupper : (⟪ι k, A k⟫_ℂ).re ≤ upper) (hgap : upper < threshold)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      threshold * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re) :
    let alpha := ⟪ι k, ι u⟫_ℂ
    let w := alpha⁻¹ • u - k
    alpha ≠ 0 ∧ ⟪ι k, ι w⟫_ℂ = 0 ∧
      ‖ι w‖ ^ 2 ≤ (upper - lower) / (threshold - lower) ∧
      0 ≤ (upper - lower) / (threshold - lower) ∧
      (upper - lower) / (threshold - lower) < 1 := by
  have ha := rayleigh_overlap_ne_zero ι A k u lam threshold hu hAu hlam hcoercive
  obtain ⟨horth, henergy⟩ := projective_error_energy_identity ι A k u lam hsym hk hAu ha
  let w := (⟪ι k, ι u⟫_ℂ)⁻¹ • u - k
  have hc := hcoercive w horth
  rw [henergy] at hc
  have he : (threshold - lam) * ‖ι w‖ ^ 2 ≤ (⟪ι k, A k⟫_ℂ).re - lam := by
    nlinarith [hc]
  have hb := projective_budget_transfer lower upper threshold lam (⟪ι k, A k⟫_ℂ).re
    (‖ι w‖ ^ 2) (sq_nonneg _) hlower hlam hupper hgap he
  exact ⟨ha, horth, hb.1, hb.2.1, hb.2.2⟩

/-- The actual readout representer is projected off the unit candidate. -/
theorem readout_orthogonal_geometry (k g : H) (hk : ‖k‖ = 1) :
    let g0 := g - ⟪k, g⟫_ℂ • k
    ⟪k, g0⟫_ℂ = 0 ∧
      ‖g0‖ ^ 2 = ‖g‖ ^ 2 - ‖⟪g, k⟫_ℂ‖ ^ 2 := by
  let g0 := g - ⟪k, g⟫_ℂ • k
  have ho : ⟪k, g0⟫_ℂ = 0 := by
    simp [g0, inner_smul_right, inner_self_eq_norm_sq_to_K, hk]
  have hd : g = ⟪k, g⟫_ℂ • k + g0 := by
    dsimp only [g0]
    abel
  have hn := norm_add_sq (𝕜 := ℂ) (⟪k, g⟫_ℂ • k) g0
  rw [← hd, inner_smul_left, ho, mul_zero] at hn
  simp only [Complex.zero_re, mul_zero, add_zero, norm_smul, hk, mul_one] at hn
  rw [norm_inner_symm (𝕜 := ℂ) k g] at hn
  exact ⟨ho, by linarith [hn]⟩

/-- Goal-oriented readout error: only the component of the readout representer
orthogonal to the candidate can see the projective error. -/
theorem centered_readout_error_bound (k g w : H) (delta : ℝ)
    (hk : ‖k‖ = 1) (horth : ⟪k, w⟫_ℂ = 0) (herr : ‖w‖ ^ 2 ≤ delta) :
    ‖⟪g, k + w⟫_ℂ - ⟪g, k⟫_ℂ‖ ^ 2 ≤
      (‖g‖ ^ 2 - ‖⟪g, k⟫_ℂ‖ ^ 2) * delta := by
  let g0 := g - ⟪k, g⟫_ℂ • k
  have hp : ⟪g0, w⟫_ℂ = ⟪g, w⟫_ℂ := by
    simp [g0, inner_smul_left, horth]
  have hc := norm_inner_le_norm (𝕜 := ℂ) g0 w
  have hsq := mul_self_le_mul_self (norm_nonneg (⟪g0, w⟫_ℂ)) hc
  have hmul := mul_le_mul_of_nonneg_left herr (sq_nonneg ‖g0‖)
  obtain ⟨_, hgeom⟩ := readout_orthogonal_geometry k g hk
  change ‖g0‖ ^ 2 = _ at hgeom
  rw [inner_add_right, add_sub_cancel_left, ← hp, ← hgeom]
  nlinarith [hsq, hmul]

/-- A strict computable readout margin excludes a zero for every error
compatible with the projective certificate. -/
theorem readout_ne_zero_of_margin (k g w : H) (delta : ℝ)
    (hk : ‖k‖ = 1) (horth : ⟪k, w⟫_ℂ = 0) (herr : ‖w‖ ^ 2 ≤ delta)
    (hmargin : (‖g‖ ^ 2 - ‖⟪g, k⟫_ℂ‖ ^ 2) * delta < ‖⟪g, k⟫_ℂ‖ ^ 2) :
    ⟪g, k + w⟫_ℂ ≠ 0 := by
  intro hz
  have h := centered_readout_error_bound k g w delta hk horth herr
  rw [hz, zero_sub, norm_neg] at h
  exact (not_le_of_gt hmargin) h

#print axioms rayleigh_projective_enclosure
#print axioms centered_readout_error_bound
#print axioms readout_ne_zero_of_margin

end D5.S3.Observer.Hankel.ProjectiveRayleighReadout
