/- GID: D5/S3/Geometry/Lorentz/KerrErgospherePenrose4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/KerrErgospherePenrose4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kerr stationary limits, horizon rotation, extraction, and equatorial orbit benchmarks. -/

import OmegaBuild.Commands
import D5.S3.Geometry.Lorentz.BlackHoleThermodynamics4D
import D5.S3.Geometry.Lorentz.SchwarzschildOpticalGeodesics4D

/-! Stationary limits, angular velocities, horizon extraction, and equatorial Kerr orbits. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D

private theorem mul_neg_iff_pos_left {x y : ℝ} (hx : 0 < x) :
    x * y < 0 ↔ y < 0 := by
  simpa only [smul_eq_mul] using (smul_neg_iff_of_pos_left (β := ℝ) hx : x • y < 0 ↔ y < 0)

private theorem div_nonneg_iff_pos_right {x y : ℝ} (hy : 0 < y) :
    0 ≤ x / y ↔ 0 ≤ x := by
  rw [div_eq_mul_inv, mul_nonneg_iff_of_pos_right (inv_pos.2 hy)]

private theorem spin_sq_bound {M a : ℝ} (hM : 0 ≤ M) (ha : |a| ≤ M) :
    a ^ 2 ≤ M ^ 2 := by
  rw [← sq_abs a]
  exact (sq_le_sq₀ (abs_nonneg _) hM).2 ha

private theorem spin_sq_strict {M a : ℝ} (hM : 0 < M) (ha : |a| < M) :
    a ^ 2 < M ^ 2 := by
  rw [← sq_abs a]
  exact (sq_lt_sq₀ (abs_nonneg _) hM.le).2 ha

def kerrDelta (M a r : ℝ) : ℝ := r ^ 2 - 2 * M * r + a ^ 2
def kerrSigma (a r θ : ℝ) : ℝ := r ^ 2 + a ^ 2 * Real.cos θ ^ 2
def kerrA (M a r θ : ℝ) : ℝ :=
  (r ^ 2 + a ^ 2) ^ 2 - a ^ 2 * kerrDelta M a r * Real.sin θ ^ 2

def g_tt (M a r θ : ℝ) : ℝ := -(1 - 2 * M * r / kerrSigma a r θ)
def g_tφ (M a r θ : ℝ) : ℝ := -(2 * M * a * r * Real.sin θ ^ 2 / kerrSigma a r θ)
def g_φφ (M a r θ : ℝ) : ℝ := kerrA M a r θ * Real.sin θ ^ 2 / kerrSigma a r θ
def g_rr (M a r θ : ℝ) : ℝ := kerrSigma a r θ / kerrDelta M a r
def g_θθ (a r θ : ℝ) : ℝ := kerrSigma a r θ

private theorem kerrA_expand (M a r θ : ℝ) :
    kerrA M a r θ = (r ^ 2 + a ^ 2) * kerrSigma a r θ +
      2 * M * r * a ^ 2 * Real.sin θ ^ 2 := by
  unfold kerrA kerrDelta kerrSigma
  linear_combination -(a ^ 2 * (r ^ 2 + a ^ 2)) * Real.sin_sq_add_cos_sq θ

theorem kerr_metric_2d_det {M a r θ : ℝ} (hσ : kerrSigma a r θ ≠ 0) :
    g_tt M a r θ * g_φφ M a r θ - g_tφ M a r θ ^ 2 =
      -kerrDelta M a r * Real.sin θ ^ 2 := by
  unfold g_tt g_tφ g_φφ
  rw [kerrA_expand]
  field_simp
  unfold kerrSigma kerrDelta
  linear_combination -(2 * M * r * a ^ 2 * Real.sin θ ^ 2) *
    (r ^ 2 + a ^ 2 * Real.cos θ ^ 2) * Real.sin_sq_add_cos_sq θ

def rPlus (M a : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - a ^ 2)
def rMinus (M a : ℝ) : ℝ := M - Real.sqrt (M ^ 2 - a ^ 2)
def rErgo (M a θ : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - a ^ 2 * Real.cos θ ^ 2)

private theorem rPlus_pos {M a : ℝ} (hM : 0 < M) : 0 < rPlus M a :=
  add_pos_of_pos_of_nonneg hM (Real.sqrt_nonneg _)

theorem kerrDelta_factorization {M a : ℝ} (ha : |a| ≤ M) (r : ℝ) :
    kerrDelta M a r = (r - rPlus M a) * (r - rMinus M a) := by
  unfold kerrDelta rPlus rMinus
  linear_combination Real.sq_sqrt (sub_nonneg.2 (spin_sq_bound ((abs_nonneg a).trans ha) ha))

private theorem delta_pos {M a r : ℝ} (ha : |a| ≤ M) (hr : rPlus M a < r) :
    0 < kerrDelta M a r := by
  rw [kerrDelta_factorization ha]
  have hle : rMinus M a ≤ rPlus M a := by
    unfold rMinus rPlus
    linarith [Real.sqrt_nonneg (M ^ 2 - a ^ 2)]
  exact mul_pos (sub_pos.2 hr) (sub_pos.2 (hle.trans_lt hr))

theorem ergosphere_strictly_outside_horizon {M a : ℝ} (ha : |a| ≤ M) (θ : ℝ) :
    rPlus M a ≤ rErgo M a θ ∧
      (a ≠ 0 → (rPlus M a < rErgo M a θ ↔ Real.sin θ ≠ 0)) := by
  have hrad : 0 ≤ M ^ 2 - a ^ 2 := sub_nonneg.2 (spin_sq_bound ((abs_nonneg a).trans ha) ha)
  have heq : M ^ 2 - a ^ 2 * Real.cos θ ^ 2 =
      M ^ 2 - a ^ 2 + a ^ 2 * Real.sin θ ^ 2 := by
    linear_combination -(a ^ 2) * Real.sin_sq_add_cos_sq θ
  unfold rPlus rErgo
  rw [heq, add_le_add_iff_left, add_lt_add_iff_left]
  refine ⟨Real.sqrt_le_sqrt (le_add_of_nonneg_right (by positivity)), ?_⟩
  intro haz
  rw [Real.sqrt_lt_sqrt_iff hrad, lt_add_iff_pos_right]
  constructor
  · intro h hs
    simp [hs] at h
  · intro hs
    exact mul_pos (sq_pos_of_ne_zero haz) (sq_pos_of_ne_zero hs)

theorem g_tt_positive_in_ergosphere {M a r θ : ℝ} (hM : 0 < M)
    (hr : rPlus M a < r) (he : r < rErgo M a θ) : 0 < g_tt M a r θ := by
  have hrp : 0 < r := (rPlus_pos hM).trans hr
  have hrs : 0 ≤ r - M := by
    unfold rPlus at hr
    linarith [Real.sqrt_nonneg (M ^ 2 - a ^ 2)]
  have hl : r - M < Real.sqrt (M ^ 2 - a ^ 2 * Real.cos θ ^ 2) := by
    unfold rErgo at he
    linarith
  have hlt := (Real.lt_sqrt hrs).1 hl
  have hσ : 0 < kerrSigma a r θ := by unfold kerrSigma; positivity
  unfold g_tt
  apply neg_pos.2 (sub_neg.2 ((one_lt_div hσ).2 ?_))
  unfold kerrSigma
  nlinarith only [hlt]

private theorem kerrA_pos {M a r : ℝ} (hM : 0 < M) (hr : 0 < r) (θ : ℝ) :
    0 < kerrA M a r θ := by
  rw [kerrA_expand]
  unfold kerrSigma
  positivity

private theorem g_φφ_pos {M a r θ : ℝ} (hM : 0 < M) (hr : 0 < r)
    (hs : Real.sin θ ≠ 0) : 0 < g_φφ M a r θ := by
  exact div_pos (mul_pos (kerrA_pos hM hr θ) (sq_pos_of_ne_zero hs)) (by
    unfold kerrSigma
    positivity)

def frameDragOmega (M a r θ : ℝ) : ℝ := -g_tφ M a r θ / g_φφ M a r θ
def horizonOmega (M a : ℝ) : ℝ := a / (2 * M * rPlus M a)

private theorem frameDrag_eq {M a r θ : ℝ} (hM : 0 < M) (hr : 0 < r)
    (hs : Real.sin θ ≠ 0) :
    frameDragOmega M a r θ = 2 * M * a * r / kerrA M a r θ := by
  have hσ : kerrSigma a r θ ≠ 0 := by unfold kerrSigma; positivity
  unfold frameDragOmega g_tφ g_φφ
  field_simp [hσ, hs, (kerrA_pos hM hr θ).ne']

private theorem horizon_radius_identity {M a : ℝ} (ha : |a| ≤ M) :
    rPlus M a ^ 2 + a ^ 2 = 2 * M * rPlus M a := by
  have hd := kerrDelta_factorization ha (rPlus M a)
  unfold kerrDelta at hd
  rw [sub_self, zero_mul] at hd
  linarith

theorem frameDrag_at_horizon_rigid {M a θ : ℝ} (hM : 0 < M) (ha : |a| ≤ M)
    (hs : Real.sin θ ≠ 0) :
    frameDragOmega M a (rPlus M a) θ = horizonOmega M a := by
  have hr := rPlus_pos (a := a) hM
  rw [frameDrag_eq hM hr hs, kerrA, kerrDelta_factorization ha, sub_self, zero_mul,
    mul_zero, zero_mul, sub_zero, horizon_radius_identity ha, horizonOmega]
  field_simp

def circularNorm (M a r θ Ω : ℝ) : ℝ :=
  g_tt M a r θ + 2 * g_tφ M a r θ * Ω + g_φφ M a r θ * Ω ^ 2

def omegaMin (M a r θ : ℝ) : ℝ :=
  frameDragOmega M a r θ - Real.sqrt (kerrDelta M a r) * |Real.sin θ| / g_φφ M a r θ

def omegaMax (M a r θ : ℝ) : ℝ :=
  frameDragOmega M a r θ + Real.sqrt (kerrDelta M a r) * |Real.sin θ| / g_φφ M a r θ

private theorem circular_factor {M a r θ : ℝ} (hM : 0 < M) (hr : 0 < r)
    (hd : 0 ≤ kerrDelta M a r) (hs : Real.sin θ ≠ 0) (Ω : ℝ) :
    circularNorm M a r θ Ω =
      g_φφ M a r θ * ((Ω - omegaMin M a r θ) * (Ω - omegaMax M a r θ)) := by
  have hg := (g_φφ_pos (a := a) hM hr hs).ne'
  have hσ : kerrSigma a r θ ≠ 0 := by unfold kerrSigma; positivity
  have hdet := kerr_metric_2d_det (M := M) hσ
  unfold circularNorm omegaMin omegaMax frameDragOmega
  field_simp [hg]
  linear_combination hdet + (Real.sin θ) ^ 2 * Real.sq_sqrt hd +
    Real.sqrt (kerrDelta M a r) ^ 2 * sq_abs (Real.sin θ)

private theorem omega_order {M a r θ : ℝ} (hM : 0 < M) (ha : |a| ≤ M)
    (hr : rPlus M a < r) (hs : Real.sin θ ≠ 0) :
    omegaMin M a r θ < omegaMax M a r θ := by
  have hg := g_φφ_pos (a := a) hM ((rPlus_pos hM).trans hr) hs
  have hp := div_pos (mul_pos (Real.sqrt_pos.2 (delta_pos ha hr)) (abs_pos.2 hs)) hg
  unfold omegaMin omegaMax
  linarith

theorem timelike_omega_window_iff {M a r θ Ω : ℝ} (hM : 0 < M) (ha : |a| ≤ M)
    (hr : rPlus M a < r) (hs : Real.sin θ ≠ 0) :
    circularNorm M a r θ Ω < 0 ↔ omegaMin M a r θ < Ω ∧ Ω < omegaMax M a r θ := by
  have hrp := (rPlus_pos hM).trans hr
  rw [circular_factor hM hrp (delta_pos ha hr).le hs,
    mul_neg_iff_pos_left (g_φφ_pos (a := a) hM hrp hs), mul_neg_iff]
  have hlt := omega_order hM ha hr hs
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨sub_pos.1 h₁, sub_neg.1 h₂⟩
    · exact ((sub_pos.1 h₂).trans ((sub_neg.1 h₁).trans hlt)).false.elim
  · rintro ⟨h₁, h₂⟩
    exact Or.inl ⟨sub_pos.2 h₁, sub_neg.2 h₂⟩

/-- An explicit congruence of the exterior metric to a diagonal form. -/
theorem kerr_exterior_metric_signature {M a r θ : ℝ} (hM : 0 < M) (ha : |a| ≤ M)
    (hr : rPlus M a < r) (hs : Real.sin θ ≠ 0) :
    let positive := g_φφ M a r θ
    let negative := -kerrDelta M a r * Real.sin θ ^ 2 / positive
    negative < 0 ∧ 0 < positive ∧ 0 < g_rr M a r θ ∧ 0 < g_θθ a r θ ∧
      ∀ t x y φ : ℝ,
        g_tt M a r θ * t ^ 2 + 2 * g_tφ M a r θ * t * φ + positive * φ ^ 2 +
            g_rr M a r θ * x ^ 2 + g_θθ a r θ * y ^ 2 =
          negative * t ^ 2 + positive * (φ - frameDragOmega M a r θ * t) ^ 2 +
            g_rr M a r θ * x ^ 2 + g_θθ a r θ * y ^ 2 := by
  dsimp only
  have hrp := (rPlus_pos hM).trans hr
  have hd := delta_pos ha hr
  have hg := g_φφ_pos (a := a) hM hrp hs
  have hσ : 0 < kerrSigma a r θ := by unfold kerrSigma; positivity
  refine ⟨div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hd)
    (sq_pos_of_ne_zero hs)) hg, hg, div_pos hσ hd, hσ, ?_⟩
  intro t x y φ
  have he := kerr_metric_2d_det (M := M) hσ.ne'
  unfold frameDragOmega
  rw [← he]
  field_simp [hg.ne']
  ring

theorem ergosphere_forbids_static_observer {M a r θ : ℝ} (ha : 0 < a) (haM : a ≤ M)
    (hr : rPlus M a < r) (he : r < rErgo M a θ) (hs : Real.sin θ ≠ 0) :
    0 < omegaMin M a r θ ∧ 0 < circularNorm M a r θ 0 ∧
      ∀ Ω : ℝ, circularNorm M a r θ Ω < 0 → 0 < Ω := by
  have hM := ha.trans_le haM
  have habs : |a| ≤ M := by rwa [abs_of_pos ha]
  have hrp := (rPlus_pos hM).trans hr
  have hg := g_φφ_pos (a := a) hM hrp hs
  have hd := delta_pos habs hr
  have hc : 0 < circularNorm M a r θ 0 := by
    simpa [circularNorm] using g_tt_positive_in_ergosphere hM hr he
  have hdrag : 0 < frameDragOmega M a r θ := by
    rw [frameDrag_eq hM hrp hs]
    exact div_pos (by positivity) (kerrA_pos hM hrp θ)
  have hmax : 0 < omegaMax M a r θ := by
    unfold omegaMax
    exact add_pos hdrag (div_pos (mul_pos (Real.sqrt_pos.2 hd) (abs_pos.2 hs)) hg)
  have hmin : 0 < omegaMin M a r θ := by
    rw [circular_factor hM hrp hd.le hs] at hc
    have hp := (mul_pos_iff_of_pos_left hg).1 hc
    have hp' : 0 < (-omegaMin M a r θ) * (-omegaMax M a r θ) := by simpa using hp
    have ht : 0 < omegaMax M a r θ * omegaMin M a r θ := by
      simpa only [neg_mul_neg, mul_comm] using hp'
    exact (mul_pos_iff_of_pos_left hmax).1 ht
  exact ⟨hmin, hc, fun Ω hΩ =>
    hmin.trans ((timelike_omega_window_iff hM habs hr hs).1 hΩ).1⟩

theorem penrose_extraction_forces_retrograde {M a E₀ Eout Ein Lin : ℝ}
    (ha : 0 < a) (haM : a ≤ M) (hfuture : 0 ≤ Ein - horizonOmega M a * Lin)
    (hEin : Ein < 0) (hsplit : E₀ = Eout + Ein) : Lin < 0 ∧ E₀ < Eout := by
  have hM := ha.trans_le haM
  have hr := rPlus_pos (a := a) hM
  have hΩ : 0 < horizonOmega M a := div_pos ha (by positivity)
  exact ⟨(mul_neg_iff_pos_left hΩ).1 (by linarith), by linarith⟩

open BlackHoleThermodynamics4D in
/-- The neutral first law compares the signs of the area and generator-energy variations. -/
theorem penrose_area_nondecrease_iff {M a t δA δJ δM : ℝ} {A J : ℝ → ℝ}
    (hM : 0 < M) (ha : |a| < M) (hA : A t = horizonArea M (a * M) 0)
    (hJ : J t = a * M) (dA : HasDerivAt A δA t) (dJ : HasDerivAt J δJ t)
    (dM : HasDerivAt (fun x => kerrNewmanMass (A x) (J x) 0) δM t) :
    (0 ≤ δA ↔ 0 ≤ δM - horizonOmega M a * δJ) ∧
      (0 ≤ δA ↔ 0 ≤ deriv (fun x => Real.sqrt (A x / (16 * Real.pi))) t) := by
  have hs : spin M (a * M) = a := by simp [spin, hM.ne']
  have hbound : 0 ^ 2 + spin M (a * M) ^ 2 < M ^ 2 := by
    simpa [hs] using spin_sq_strict hM ha
  have hΩ : angularVelocity M (a * M) 0 = horizonOmega M a := by
    have he := rPlus_sq_add_a_sq_eq hbound.le
    dsimp [angularVelocity, horizonFactor, horizonOmega]
    rw [he, hs]
    simp [BlackHoleThermodynamics4D.rPlus, horizonGap, hs, rPlus]
  have d := kerrNewman_first_law hM hbound.le hA hJ rfl dA dJ (hasDerivAt_const t 0)
  have hmass := dM.unique d
  rw [hΩ, mul_zero, add_zero] at hmass
  have hκ := surfaceGravity_pos_of_subextremal hM hbound
  have hcoeff : 0 < surfaceGravity M (a * M) 0 / (8 * Real.pi) :=
    div_pos hκ (by positivity)
  have hApos : 0 < A t := hA ▸ horizonArea_pos hM
  have hratio : 0 < A t / (16 * Real.pi) := div_pos hApos (by positivity)
  have dirr := (dA.div_const (16 * Real.pi)).sqrt hratio.ne'
  refine ⟨?_, ?_⟩
  · rw [hmass, add_sub_cancel_right, mul_nonneg_iff_of_pos_left hcoeff]
  · rw [dirr.deriv]
    have hden : 0 < 2 * Real.sqrt (A t / (16 * Real.pi)) := by positivity
    rw [div_nonneg_iff_pos_right hden, div_nonneg_iff_pos_right (by positivity : 0 < 16 * Real.pi)]

def horizonAbsorption (M a ω m coefficient : ℝ) : ℝ :=
  coefficient * (ω * (ω - m * horizonOmega M a))

theorem superradiance_condition_iff (M a m : ℝ) {ω coefficient : ℝ}
    (hω : 0 < ω) (hc : 0 < coefficient) :
    horizonAbsorption M a ω m coefficient < 0 ↔ ω < m * horizonOmega M a := by
  rw [horizonAbsorption, mul_neg_iff_pos_left hc, mul_neg_iff_pos_left hω, sub_neg]

def kerrPhotonPoly (M a r : ℝ) : ℝ := r * (r - 3 * M) ^ 2 - 4 * M * a ^ 2

theorem kerr_photon_orbit_benchmarks {M r : ℝ} (hr : 0 < r) :
    (kerrPhotonPoly M 0 r = 0 ↔ r = 3 * M) ∧
      (kerrPhotonPoly M 0 r = 0 ↔ deriv (SchwarzschildOpticalGeodesics4D.nullPotential M) r = 0) ∧
      kerrPhotonPoly M M r = (r - M) ^ 2 * (r - 4 * M) ∧
      (kerrPhotonPoly M M r = 0 ↔ r = M ∨ r = 4 * M) := by
  have hfactor : kerrPhotonPoly M M r = (r - M) ^ 2 * (r - 4 * M) := by
    unfold kerrPhotonPoly
    ring
  have hSchwarzschild : kerrPhotonPoly M 0 r = 0 ↔ r = 3 * M := by
    simp [kerrPhotonPoly, hr.ne', sub_eq_zero]
  refine ⟨hSchwarzschild,
    hSchwarzschild.trans (SchwarzschildOpticalGeodesics4D.photon_sphere_unique hr).symm,
    hfactor, ?_⟩
  rw [hfactor, mul_eq_zero, sq_eq_zero_iff, sub_eq_zero, sub_eq_zero]

def kerrISCOPoly (M a s r : ℝ) : ℝ :=
  r ^ 2 - 6 * M * r + 8 * s * a * Real.sqrt (M * r) - 3 * a ^ 2

/-- The unsquared equatorial photon condition retains the sense of rotation. -/
def circularPhotonEquation (M a s r : ℝ) : ℝ :=
  r * (r - 3 * M) + 2 * s * a * Real.sqrt (M * r)

private theorem sqrt_mass_radius {M r : ℝ} (hM : 0 < M) (hr : 0 ≤ r) :
    Real.sqrt (M * r) = M * Real.sqrt (r / M) := by
  rw [show M * r = M ^ 2 * (r / M) by field_simp [hM.ne'], Real.sqrt_mul (sq_nonneg M),
    Real.sqrt_sq hM.le]

private theorem signed_photon_root {M a s r : ℝ} (hM : 0 < M) (hr : 0 < r)
    (hs : s ^ 2 = 1) (h : circularPhotonEquation M a s r = 0) :
    kerrPhotonPoly M a r = 0 := by
  have hl : r * (r - 3 * M) = -(2 * s * a * Real.sqrt (M * r)) := by
    unfold circularPhotonEquation at h
    linarith only [h]
  have hh := congrArg (fun x : ℝ => x ^ 2) hl
  simp only [mul_pow, neg_sq, hs, mul_one, Real.sq_sqrt (mul_nonneg hM.le hr.le)] at hh
  rw [← mul_right_inj' hr.ne', mul_zero]
  unfold kerrPhotonPoly
  linear_combination hh

theorem extremal_photon_orbit_directions {M r : ℝ} (hM : 0 < M) (hr : 0 < r) :
    (circularPhotonEquation M M 1 r = 0 ↔ r = M) ∧
      (circularPhotonEquation M M (-1) r = 0 ↔ r = 4 * M) := by
  have hMroot : Real.sqrt (M * M) = M := by rw [← pow_two, Real.sqrt_sq hM.le]
  have h4root : Real.sqrt (M * (4 * M)) = 2 * M := by
    rw [show M * (4 * M) = (2 * M) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hpro : circularPhotonEquation M M 1 M = 0 := by
    unfold circularPhotonEquation
    rw [hMroot]
    ring
  have hretro : circularPhotonEquation M M (-1) (4 * M) = 0 := by
    unfold circularPhotonEquation
    rw [h4root]
    ring
  have hp := (kerr_photon_orbit_benchmarks (M := M) hr).2.2.2
  constructor
  · refine ⟨fun h => ?_, fun he => he.symm ▸ hpro⟩
    rcases hp.mp (signed_photon_root hM hr (by norm_num) h) with he | he
    · exact he
    · rw [he, circularPhotonEquation, h4root] at h
      nlinarith only [h, sq_pos_of_pos hM]
  · refine ⟨fun h => ?_, fun he => he.symm ▸ hretro⟩
    rcases hp.mp (signed_photon_root hM hr (by norm_num) h) with he | he
    · rw [he, circularPhotonEquation, hMroot] at h
      nlinarith only [h, sq_pos_of_pos hM]
    · exact he

private theorem iscoPoly_dimensionless {M a s r : ℝ} (hM : 0 < M) (hr : 0 ≤ r)
    (hs : s ^ 2 = 1) :
    let x := Real.sqrt (r / M)
    kerrISCOPoly M a s r =
      M ^ 2 * (x ^ 4 - 6 * x ^ 2 + 8 * (s * a / M) * x - 3 * (s * a / M) ^ 2) := by
  let x := Real.sqrt (r / M)
  change kerrISCOPoly M a s r =
    M ^ 2 * (x ^ 4 - 6 * x ^ 2 + 8 * (s * a / M) * x - 3 * (s * a / M) ^ 2)
  have hx : x ^ 2 * M = r :=
    (eq_div_iff hM.ne').1 (Real.sq_sqrt (div_nonneg hr hM.le))
  unfold kerrISCOPoly
  rw [sqrt_mass_radius hM hr]
  change r ^ 2 - 6 * M * r + 8 * s * a * (M * x) - 3 * a ^ 2 = _
  rw [← hx]
  field_simp [hM.ne']
  rw [hs]
  ring

theorem extremal_isco_radii_unique {M r : ℝ} (hM : 0 < M) (hr : 0 < r) :
    (kerrISCOPoly M M 1 r = 0 ↔ r = M) ∧
      (kerrISCOPoly M M (-1) r = 0 ↔ r = 9 * M) := by
  let x := Real.sqrt (r / M)
  have hx : 0 < x := Real.sqrt_pos.2 (div_pos hr hM)
  have hsq : x ^ 2 = r / M := Real.sq_sqrt (div_nonneg hr.le hM.le)
  have hplus := iscoPoly_dimensionless (a := M) (s := 1) hM hr.le (by norm_num)
  have hminus := iscoPoly_dimensionless (a := M) (s := -1) hM hr.le (by norm_num)
  change kerrISCOPoly M M 1 r =
    M ^ 2 * (x ^ 4 - 6 * x ^ 2 + 8 * (1 * M / M) * x - 3 * (1 * M / M) ^ 2) at hplus
  change kerrISCOPoly M M (-1) r =
    M ^ 2 * (x ^ 4 - 6 * x ^ 2 + 8 * (-1 * M / M) * x - 3 * (-1 * M / M) ^ 2) at hminus
  simp only [one_mul, div_self hM.ne', neg_mul, neg_div] at hplus hminus
  rw [show x ^ 4 - 6 * x ^ 2 + 8 * 1 * x - 3 * 1 ^ 2 = (x - 1) ^ 3 * (x + 3) by ring]
    at hplus
  rw [show x ^ 4 - 6 * x ^ 2 + 8 * (-1) * x - 3 * (-1) ^ 2 = (x + 1) ^ 3 * (x - 3) by ring]
    at hminus
  rw [hplus, hminus]
  have hx1 : x + 1 ≠ 0 := by positivity
  have hx3 : x + 3 ≠ 0 := by positivity
  simp only [mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0),
    pow_eq_zero_iff (by decide : 3 ≠ 0), hM.ne', hx1, hx3, false_or, or_false, sub_eq_zero]
  constructor
  · rw [← sq_eq_sq₀ hx.le (by norm_num : (0 : ℝ) ≤ 1), hsq]
    simp [div_eq_iff hM.ne']
  · rw [← sq_eq_sq₀ hx.le (by norm_num : (0 : ℝ) ≤ 3), hsq, div_eq_iff hM.ne']
    norm_num

/-- Binding efficiency in terms of the dimensionless ISCO radius. -/
def iscoEfficiency (radius : ℝ) : ℝ := 1 - Real.sqrt (1 - 2 / (3 * radius))

theorem kerr_isco_benchmarks_and_binding_efficiency {M r : ℝ} (s : ℝ) (hM : 0 < M)
    (hr : 0 < r) :
    (kerrISCOPoly M 0 s r = 0 ↔ r = 6 * M) ∧
      kerrISCOPoly M M 1 M = 0 ∧ kerrISCOPoly M M (-1) (9 * M) = 0 ∧
      iscoEfficiency 6 = 1 - 2 * Real.sqrt 2 / 3 ∧
      iscoEfficiency 1 = 1 - 1 / Real.sqrt 3 ∧
      iscoEfficiency 9 = 1 - 5 / (3 * Real.sqrt 3) ∧
      (0 < iscoEfficiency 9 ∧ iscoEfficiency 9 < iscoEfficiency 6 ∧
        iscoEfficiency 6 < iscoEfficiency 1 ∧ iscoEfficiency 1 < 1 / 2) := by
  have hs₂ : 0 < Real.sqrt 2 := by positivity
  have hs₃ : 0 < Real.sqrt 3 := by positivity
  have h₂ : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h₃ : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have h9 : Real.sqrt (M * (9 * M)) = 3 * M := by
    rw [show M * (9 * M) = (3 * M) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show kerrISCOPoly M 0 s r = r * (r - 6 * M) by unfold kerrISCOPoly; ring]
    simp [hr.ne', sub_eq_zero]
  · unfold kerrISCOPoly
    rw [← pow_two M, Real.sqrt_sq hM.le]
    ring
  · unfold kerrISCOPoly
    rw [h9]
    ring
  · unfold iscoEfficiency
    congr 1
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
    rw [Real.sq_sqrt (by norm_num)]
    nlinarith only [h₂]
  · unfold iscoEfficiency
    congr 1
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
    rw [Real.sq_sqrt (by norm_num), div_pow, h₃]
    norm_num
  · unfold iscoEfficiency
    congr 1
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
    rw [Real.sq_sqrt (by norm_num), div_pow, mul_pow, h₃]
    norm_num
  · unfold iscoEfficiency
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [sub_pos]
      exact (Real.sqrt_lt (by norm_num) zero_le_one).2 (by norm_num)
    · rw [sub_lt_sub_iff_left]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    · rw [sub_lt_sub_iff_left]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    · have h : (1 / 2 : ℝ) < Real.sqrt (1 - 2 / (3 * 1)) :=
        (Real.lt_sqrt (by norm_num)).2 (by norm_num)
      linarith

/-- Specific energy for an equatorial circular timelike geodesic, in units
where the mass is one and the radial variable is the square root of the radius.
The spin argument is signed according to the orbital orientation. -/
def circularOrbitEnergy (spin x : ℝ) : ℝ :=
  (x ^ 3 - 2 * x + spin) / (x * Real.sqrt (x * (x ^ 3 - 3 * x + 2 * spin)))

/-- At a marginally stable circular orbit the energy squared depends only on
the radius. The sign selects the positive-energy branch. -/
theorem isco_efficiency_eq_orbit_binding {M a r s : ℝ} (hM : 0 < M) (hr : 0 < r)
    (hs : s ^ 2 = 1) (hisco : kerrISCOPoly M a s r = 0)
    (htimelike : 0 < let x := Real.sqrt (r / M); x ^ 3 - 3 * x + 2 * (s * a / M))
    (henergy : 0 ≤ let x := Real.sqrt (r / M); x ^ 3 - 2 * x + (s * a / M)) :
    iscoEfficiency (r / M) = 1 - circularOrbitEnergy (s * a / M) (Real.sqrt (r / M)) := by
  let x := Real.sqrt (r / M)
  let b := s * a / M
  change 0 < x ^ 3 - 3 * x + 2 * b at htimelike
  change 0 ≤ x ^ 3 - 2 * x + b at henergy
  change iscoEfficiency (r / M) = 1 - circularOrbitEnergy b x
  have hxpos : 0 < x := Real.sqrt_pos.2 (div_pos hr hM)
  have hx : x ^ 2 = r / M := Real.sq_sqrt (div_nonneg hr.le hM.le)
  have hpoly : x ^ 4 - 6 * x ^ 2 + 8 * b * x - 3 * b ^ 2 = 0 := by
    rw [iscoPoly_dimensionless hM hr.le hs] at hisco
    exact (mul_eq_zero.mp hisco).resolve_left (pow_ne_zero 2 hM.ne')
  have hd : 0 < x * (x ^ 3 - 3 * x + 2 * b) := mul_pos hxpos htimelike
  have he : circularOrbitEnergy b x ^ 2 = 1 - 2 / (3 * x ^ 2) := by
    unfold circularOrbitEnergy
    rw [div_pow, mul_pow, Real.sq_sqrt hd.le]
    apply (div_eq_iff (mul_ne_zero (pow_ne_zero 2 hxpos.ne') hd.ne')).2
    have hden : (3 : ℝ) * x ^ 2 ≠ 0 := by positivity
    rw [show 1 - 2 / (3 * x ^ 2) = (3 * x ^ 2 - 2) / (3 * x ^ 2) by
      field_simp [hxpos.ne']]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hden).2
    linear_combination -(x ^ 2) * hpoly
  have hE : 0 ≤ circularOrbitEnergy b x := by
    unfold circularOrbitEnergy
    exact div_nonneg henergy (by positivity)
  unfold iscoEfficiency
  rw [← hx, ← he, Real.sqrt_sq hE]

/-- The extremal prograde energy is obtained as an exterior limit at the
degenerate circular-orbit radius. -/
theorem extremal_prograde_energy_limit :
    Tendsto (circularOrbitEnergy 1) (𝓝[>] 1) (𝓝 (1 / Real.sqrt 3)) := by
  let regular (x : ℝ) := (x ^ 2 + x - 1) / (x * Real.sqrt (x * (x + 2)))
  have heq : circularOrbitEnergy 1 =ᶠ[𝓝[>] (1 : ℝ)] regular := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : 1 < x := hx
    have hxp : 0 < x := by linarith
    have hp : 0 < x - 1 := sub_pos.2 hx'
    have harg : 0 < x * (x + 2) := mul_pos hxp (by positivity)
    dsimp [circularOrbitEnergy, regular]
    rw [show x ^ 3 - 2 * x + 1 = (x - 1) * (x ^ 2 + x - 1) by ring,
      show x * (x ^ 3 - 3 * x + 2 * 1) = (x - 1) ^ 2 * (x * (x + 2)) by ring,
      Real.sqrt_mul (sq_nonneg (x - 1)), Real.sqrt_sq hp.le]
    field_simp [hxp.ne', hp.ne', (Real.sqrt_pos.2 harg).ne']
  have hden : (1 : ℝ) * Real.sqrt (1 * (1 + 2)) ≠ 0 := by
    exact mul_ne_zero one_ne_zero (Real.sqrt_ne_zero'.2 (by positivity))
  have hc : ContinuousAt regular 1 := by
    have hn : ContinuousAt (fun x : ℝ => x ^ 2 + x - 1) (1 : ℝ) := by fun_prop
    have hd : ContinuousAt (fun x : ℝ => x * Real.sqrt (x * (x + 2))) (1 : ℝ) := by fun_prop
    exact hn.div₀ hd hden
  have hv : regular 1 = 1 / Real.sqrt 3 := by norm_num [regular]
  rw [← hv, tendsto_congr' heq]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

end D5.S3.Geometry.Lorentz.KerrErgospherePenrose4D
