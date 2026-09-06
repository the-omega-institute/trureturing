/- GID: D5/S3/Weil/ZetaBridge/WeilProjectiveRayleighCapture
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilProjectiveRayleighCapture
   mirror-E: none(waiver:operator-domain-projective-estimate)
   anchors: []
   digest: Derive a sharp complex projective eigenvector error budget from a candidate energy ceiling and coercivity on its orthogonal complement. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Projective capture from a variational enclosure

The action A is defined only on the linear domain D. No boundedness,
completeness, compact resolvent, existence of a ground state, or spectral
claim about a concrete Weil operator is assumed implicitly.

This is the complex/projective continuation of the real estimate in
WeilRayleighEnclosureModeCapture. The denominator is threshold - lower.
The eigenvector need not be normalized. Its nonzero overlap with the
candidate, and candidate energy >= the selected eigenvalue, are derived.

The intended analytic target is the ground-vector approximation problem in
Connes--Consani--Moscovici, Zeta Spectral Triples, arXiv:2511.22755v1,
Section 8. Compare the classical Rayleigh/angle estimates of Zhu--Argentati--
Knyazev, SIAM J. Matrix Anal. Appl. 34 (2013), 244--256. The two-dimensional
energy identity is classical; no mathematical priority is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilProjectiveRayleighCapture

open scoped InnerProductSpace

variable {H D : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [AddCommGroup D] [Module ℂ D]

private theorem eigen_energy (ι A : D →ₗ[ℂ] H) (u : D) (lam : ℝ)
    (heigen : A u = (lam : ℂ) • ι u) :
    (⟪ι u, A u⟫_ℂ).re = lam * ‖ι u‖ ^ 2 := by
  rw [heigen, inner_smul_right, inner_self_eq_norm_sq_to_K]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Any nonzero eigenvector below the candidate-orthogonal threshold has
nonzero overlap with that candidate. Normalization and symmetry are not
needed for this exclusion argument. -/
theorem eigen_overlap_ne_zero
    (ι A : D →ₗ[ℂ] H) (k u : D) (lam threshold : ℝ)
    (hu : ι u ≠ 0)
    (heigen : A u = (lam : ℂ) • ι u)
    (hgap : lam < threshold)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      threshold * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re) :
    ⟪ι k, ι u⟫_ℂ ≠ 0 := by
  intro hzero
  have h := hcoercive u hzero
  rw [eigen_energy ι A u lam heigen] at h
  have hnorm : 0 < ‖ι u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hstrict := mul_pos (sub_pos.mpr hgap) hnorm
  nlinarith

/-- Normalize by the actual candidate overlap. The remaining vector is
orthogonal to k and its energy has an exact eigenvalue identity, including
both complex mixed terms. -/
theorem projective_error_energy_identity
    (ι A : D →ₗ[ℂ] H) (k u : D) (lam : ℝ)
    (hsymmetric : ∀ x y : D, ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ)
    (hk : ‖ι k‖ = 1)
    (heigen : A u = (lam : ℂ) • ι u)
    (hoverlap : ⟪ι k, ι u⟫_ℂ ≠ 0) :
    let w := (⟪ι k, ι u⟫_ℂ)⁻¹ • u - k
    ⟪ι k, ι w⟫_ℂ = 0 ∧
      (⟪ι w, A w⟫_ℂ).re =
        lam * ‖ι w‖ ^ 2 + (⟪ι k, A k⟫_ℂ).re - lam := by
  let alpha : ℂ := ⟪ι k, ι u⟫_ℂ
  let p : D := alpha⁻¹ • u
  let w : D := p - k
  have ha : alpha ≠ 0 := hoverlap
  have hpimage : ι p = alpha⁻¹ • ι u := by simp only [p, map_smul]
  have hpinner : ⟪ι k, ι p⟫_ℂ = 1 := by
    rw [hpimage, inner_smul_right]
    change alpha⁻¹ * alpha = 1
    exact inv_mul_cancel₀ ha
  have hkself : ⟪ι k, ι k⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hk]
    norm_num
  have horth : ⟪ι k, ι w⟫_ℂ = 0 := by
    rw [show ι w = ι p - ι k by simp only [w, map_sub],
      inner_sub_right, hpinner, hkself, sub_self]
  have horth' : ⟪ι w, ι k⟫_ℂ = 0 := inner_eq_zero_symm.mp horth
  have hpdecomp : p = k + w := by simp [w]
  have hpaction : A p = A k + A w := by rw [hpdecomp, map_add]
  have hpimage' : ι p = ι k + ι w := by rw [hpdecomp, map_add]
  have hpeigen : A p = (lam : ℂ) • ι p := by
    simp only [p, map_smul, heigen, smul_smul]
    rw [mul_comm (alpha⁻¹) (lam : ℂ)]
  have hkcross :
      (⟪ι k, A k⟫_ℂ).re + (⟪ι k, A w⟫_ℂ).re = lam := by
    calc
      _ = (⟪ι k, A p⟫_ℂ).re := by
        rw [hpaction, inner_add_right, Complex.add_re]
      _ = lam := by rw [hpeigen, inner_smul_right, hpinner, mul_one]; rfl
  have hwinner : ⟪ι w, ι p⟫_ℂ = (‖ι w‖ : ℂ) ^ 2 := by
    rw [hpimage', inner_add_right, horth', zero_add, inner_self_eq_norm_sq_to_K]
  have hwcross :
      (⟪ι w, A k⟫_ℂ).re + (⟪ι w, A w⟫_ℂ).re = lam * ‖ι w‖ ^ 2 := by
    calc
      _ = (⟪ι w, A p⟫_ℂ).re := by
        rw [hpaction, inner_add_right, Complex.add_re]
      _ = _ := by
        rw [hpeigen, inner_smul_right, hwinner,
          ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsymcross : (⟪ι w, A k⟫_ℂ).re = (⟪ι k, A w⟫_ℂ).re := by
    rw [hsymmetric w k]
    exact inner_re_symm _ _
  have henergy : (⟪ι w, A w⟫_ℂ).re =
      lam * ‖ι w‖ ^ 2 + (⟪ι k, A k⟫_ℂ).re - lam := by
    rw [hsymcross] at hwcross
    linarith
  exact ⟨horth, henergy⟩

/-- Sharp complex projective enclosure on a possibly unbounded operator
 domain. The candidate energy lower bound and nonzero overlap are derived.
The comparison threshold and certified spectral lower bound stay distinct. -/
theorem projective_rayleigh_enclosure
    (ι A : D →ₗ[ℂ] H) (k u : D)
    (lower upper threshold lam : ℝ)
    (hsymmetric : ∀ x y : D, ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ)
    (hk : ‖ι k‖ = 1) (hu : ι u ≠ 0)
    (heigen : A u = (lam : ℂ) • ι u)
    (hlower : lower ≤ lam) (hlam : lam < threshold)
    (hupper : (⟪ι k, A k⟫_ℂ).re ≤ upper)
    (hthreshold : upper < threshold)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      threshold * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re) :
    let w := (⟪ι k, ι u⟫_ℂ)⁻¹ • u - k
    ⟪ι k, ι u⟫_ℂ ≠ 0 ∧
      lam ≤ (⟪ι k, A k⟫_ℂ).re ∧
      (threshold - lam) * ‖ι w‖ ^ 2 ≤ (⟪ι k, A k⟫_ℂ).re - lam ∧
      (threshold - lower) * ‖ι w‖ ^ 2 ≤ upper - lower ∧
      ‖ι w‖ ^ 2 ≤ (upper - lower) / (threshold - lower) ∧
      0 ≤ (upper - lower) / (threshold - lower) ∧
      (upper - lower) / (threshold - lower) < 1 := by
  let w : D := (⟪ι k, ι u⟫_ℂ)⁻¹ • u - k
  have ha := eigen_overlap_ne_zero ι A k u lam threshold hu heigen hlam hcoercive
  obtain ⟨horth, henergy⟩ :=
    projective_error_energy_identity ι A k u lam hsymmetric hk heigen ha
  have hc := hcoercive w horth
  rw [henergy] at hc
  have hgap : 0 < threshold - lam := sub_pos.mpr hlam
  have hgaplower : 0 < threshold - lower := by linarith
  have he : 0 ≤ ‖ι w‖ ^ 2 := sq_nonneg _
  have hexact : (threshold - lam) * ‖ι w‖ ^ 2 ≤ (⟪ι k, A k⟫_ℂ).re - lam := by
    linarith
  have hcand : lam ≤ (⟪ι k, A k⟫_ℂ).re := by
    have hp := mul_nonneg hgap.le he
    linarith
  have hgapbound : (threshold - lam) * ‖ι w‖ ^ 2 ≤ upper - lam := by
    linarith
  have heless : ‖ι w‖ ^ 2 < 1 := by
    have hless : (threshold - lam) * ‖ι w‖ ^ 2 < (threshold - lam) * 1 := by
      linarith
    exact (mul_lt_mul_left hgap).mp hless
  have hle : (threshold - lower) * ‖ι w‖ ^ 2 ≤ upper - lower := by
    have hm := mul_le_mul_of_nonneg_left heless.le (sub_nonneg.mpr hlower)
    nlinarith
  have hratio : ‖ι w‖ ^ 2 ≤ (upper - lower) / (threshold - lower) := by
    exact (le_div_iff₀ hgaplower).mpr (by simpa only [mul_comm] using hle)
  have hwidth : 0 ≤ upper - lower := by linarith
  have hratio0 : 0 ≤ (upper - lower) / (threshold - lower) :=
    div_nonneg hwidth hgaplower.le
  have hratio1 : (upper - lower) / (threshold - lower) < 1 := by
    apply (div_lt_iff₀ hgaplower).mpr
    linarith
  exact ⟨ha, hcand, hexact, hle, hratio, hratio0, hratio1⟩

/-- Exact arithmetic on the stated PR #5602 energy enclosure. This checks
 the implication between rational constants, not the analytic enclosure itself. -/
theorem prime3_projective_ratio :
    (((560909 : ℝ) / 10000000000000 - 103 / 2000000000) /
      (1 / 200000 - 103 / 2000000000)) = 15303 / 16495000 ∧
      (15303 : ℝ) / 16495000 < (61 / 2000) ^ 2 := by
  constructor <;> norm_num

/-- Convert the exact projective-square budget to the published decimal-free
norm radius. No zeta computation or spectral premise is hidden here. -/
theorem norm_lt_prime3_radius (x : H)
    (hx : ‖x‖ ^ 2 ≤ (15303 : ℝ) / 16495000) : ‖x‖ < 61 / 2000 := by
  have hs := prime3_projective_ratio.2
  nlinarith [norm_nonneg x]

#print axioms eigen_overlap_ne_zero
#print axioms projective_error_energy_identity
#print axioms projective_rayleigh_enclosure
#print axioms prime3_projective_ratio
#print axioms norm_lt_prime3_radius

end D5.S3.Weil.ZetaBridge.WeilProjectiveRayleighCapture

end
