/- GID: D5/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/SchwarzschildOpticalGeodesics4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Schwarzschild photon sphere, shadow, ISCO, redshift, and weak-field deflection. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace D5.S3.Geometry.Lorentz.SchwarzschildOpticalGeodesics4D

def nullPotential (M r : ℝ) : ℝ := (1 - 2 * M / r) / r ^ 2

theorem nullPotential_hasDerivAt {M r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (nullPotential M) (2 * (3 * M - r) / r ^ 4) r := by
  unfold nullPotential
  have h1 : HasDerivAt (fun x : ℝ => 1 - 2 * M / x) (2 * M / r ^ 2) r := by
    change HasDerivAt ((fun _ : ℝ => 1) - (fun _ : ℝ => 2 * M) / id) _ r
    have hdiv := (hasDerivAt_const r (2 * M)).div (hasDerivAt_id r) hr
    have hsub := HasDerivAt.sub (hasDerivAt_const r 1) hdiv
    convert hsub using 1
    simp [id, div_eq_mul_inv]
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    change HasDerivAt (id ^ 2) _ r
    convert HasDerivAt.pow (hasDerivAt_id r) 2 using 1; norm_num
  have h := h1.div h2 (by positivity : r ^ 2 ≠ 0)
  convert h using 1
  field_simp
  ring

theorem photon_sphere_unique {M r : ℝ} (hr : 0 < r) :
    deriv (nullPotential M) r = 0 ↔ r = 3 * M := by
  have hd := (nullPotential_hasDerivAt (M := M) hr.ne').deriv
  rw [hd]
  constructor
  · intro h
    field_simp at h
    linarith
  · rintro rfl
    ring

theorem photon_sphere_strict_global_max {M r : ℝ} (hM : 0 < M) (hr : 0 < r) :
    nullPotential M r ≤ 1 / (27 * M ^ 2) ∧
      (nullPotential M r = 1 / (27 * M ^ 2) ↔ r = 3 * M) := by
  have hM0 : M ≠ 0 := hM.ne'
  have hr0 : r ≠ 0 := hr.ne'
  have hid : 1 / (27 * M ^ 2) - nullPotential M r =
      (r - 3 * M) ^ 2 * (r + 6 * M) / (27 * M ^ 2 * r ^ 3) := by
    unfold nullPotential
    field_simp [hM0, hr0]
    ring
  have hden : 0 < 27 * M ^ 2 * r ^ 3 := by positivity
  have hfactor : 0 ≤ (r - 3 * M) ^ 2 * (r + 6 * M) := by positivity
  constructor
  · have hnon : 0 ≤ (r - 3 * M) ^ 2 * (r + 6 * M) /
        (27 * M ^ 2 * r ^ 3) := div_nonneg hfactor hden.le
    linarith [hid]
  · constructor
    · intro h
      have hz : (r - 3 * M) ^ 2 * (r + 6 * M) = 0 := by
        have : (r - 3 * M) ^ 2 * (r + 6 * M) /
            (27 * M ^ 2 * r ^ 3) = 0 := by linarith [hid, h]
        exact (div_eq_zero_iff).mp this |>.resolve_right (by positivity)
      have hpos : 0 < r + 6 * M := by positivity
      have : (r - 3 * M) ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_right hpos.ne'
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)
    · rintro rfl
      have : 1 / (27 * M ^ 2) - nullPotential M (3 * M) = 0 := by
        rw [hid]
        ring
      linarith

theorem photon_sphere_unstable {M : ℝ} (hM : 0 < M) :
    deriv (deriv (nullPotential M)) (3 * M) = -2 / (81 * M ^ 4) ∧
      deriv (deriv (nullPotential M)) (3 * M) < 0 := by
  have hp : 3 * M ≠ 0 := by positivity
  have hfirst : ∀ x : ℝ, x ≠ 0 →
      deriv (nullPotential M) x = 2 * (3 * M - x) / x ^ 4 := by
    intro x hx
    exact (nullPotential_hasDerivAt hx).deriv
  have hder : HasDerivAt (fun x : ℝ => 2 * (3 * M - x) / x ^ 4)
      (-2 / (81 * M ^ 4)) (3 * M) := by
    have hn : HasDerivAt (fun x : ℝ => 2 * (3 * M - x)) (-2) (3 * M) := by
      have h := HasDerivAt.const_mul 2
        (HasDerivAt.sub (hasDerivAt_const (3 * M) (3 * M)) (hasDerivAt_id (3 * M)))
      convert h using 1
      · funext x
        simp [id]
      · norm_num
    have hd : HasDerivAt (fun x : ℝ => x ^ 4) (4 * (3 * M) ^ 3) (3 * M) := by
      change HasDerivAt (id ^ 4) _ (3 * M)
      convert HasDerivAt.pow (hasDerivAt_id (3 * M)) 4 using 1; norm_num
    have h := hn.div hd (by positivity : (3 * M) ^ 4 ≠ 0)
    convert h using 1
    field_simp [hM.ne']
    ring
  have heq : (fun x => deriv (nullPotential M) x) =ᶠ[nhds (3 * M)]
      (fun x => 2 * (3 * M - x) / x ^ 4) := by
    filter_upwards [eventually_ne_nhds hp] with x hx
    exact hfirst x hx
  have hsecond : deriv (deriv (nullPotential M)) (3 * M) = -2 / (81 * M ^ 4) := by
    rw [heq.deriv_eq]
    exact hder.deriv
  refine ⟨hsecond, ?_⟩
  rw [hsecond]
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

theorem shadow_critical_impact_eq {M : ℝ} (hM : 0 < M) :
    (nullPotential M (3 * M))⁻¹ = 27 * M ^ 2 ∧
      Real.sqrt ((nullPotential M (3 * M))⁻¹) = 3 * Real.sqrt 3 * M := by
  have hM0 : M ≠ 0 := hM.ne'
  have hpot : nullPotential M (3 * M) = 1 / (27 * M ^ 2) := by
    unfold nullPotential
    field_simp [hM0]
    ring
  constructor
  · rw [hpot]
    field_simp [hM0]
  · rw [hpot]
    have hs3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    have hs : Real.sqrt (27 * M ^ 2) = 3 * Real.sqrt 3 * M := by
      have he : 27 * M ^ 2 = (3 * Real.sqrt 3 * M) ^ 2 := by
        rw [show (3 * Real.sqrt 3 * M) ^ 2 = 9 * (Real.sqrt 3) ^ 2 * M ^ 2 by ring, hs3]
        ring
      rw [he, Real.sqrt_sq_eq_abs, abs_of_pos]
      positivity
    convert hs using 1
    field_simp [hM0]

theorem shadow_capture_iff {M b : ℝ} (hM : 0 < M) (hb : 0 < b) :
    b < 3 * Real.sqrt 3 * M ↔ nullPotential M (3 * M) < (b ^ 2)⁻¹ := by
  have hbcrit : 0 < 3 * Real.sqrt 3 * M := by positivity
  have hcritical := shadow_critical_impact_eq hM
  have hc : (3 * Real.sqrt 3 * M) ^ 2 = 27 * M ^ 2 := by
    rw [← hcritical.2, hcritical.1, Real.sq_sqrt (by positivity)]
  have hp : nullPotential M (3 * M) = (27 * M ^ 2)⁻¹ := by
    rw [← hcritical.1, inv_inv]
  rw [hp, inv_lt_inv₀ (by positivity : 0 < 27 * M ^ 2) (by positivity : 0 < b ^ 2), ← hc]
  exact (sq_lt_sq₀ hb.le hbcrit.le).symm

def timePotential (M L r : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 - 2 * M / r) * (1 + L ^ 2 / r ^ 2)

theorem timePotential_hasDerivAt {M L r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (timePotential M L)
      ((M * r ^ 2 - L ^ 2 * (r - 3 * M)) / r ^ 4) r := by
  unfold timePotential
  have hA : HasDerivAt (fun x : ℝ => 1 - 2 * M / x) (2 * M / r ^ 2) r := by
    change HasDerivAt ((fun _ : ℝ => 1) - (fun _ : ℝ => 2 * M) / id) _ r
    have hdiv := (hasDerivAt_const r (2 * M)).div (hasDerivAt_id r) hr
    have hsub := HasDerivAt.sub (hasDerivAt_const r 1) hdiv
    convert hsub using 1
    simp [id, div_eq_mul_inv]
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    change HasDerivAt (id ^ 2) _ r
    convert HasDerivAt.pow (hasDerivAt_id r) 2 using 1; norm_num
  have hB : HasDerivAt (fun x : ℝ => 1 + L ^ 2 / x ^ 2)
      (-2 * L ^ 2 / r ^ 3) r := by
    have hd := (hasDerivAt_const r (L ^ 2)).div hpow (by positivity : r ^ 2 ≠ 0)
    have hsum := HasDerivAt.add (hasDerivAt_const r 1) hd
    convert hsum using 1
    field_simp
    ring
  have h := HasDerivAt.const_mul (1 / 2 : ℝ) (HasDerivAt.mul hA hB)
  convert h using 1
  · funext x
    simp only [Pi.mul_apply]
    ring
  · field_simp
    ring

theorem circular_orbit_angMom_iff {M L r : ℝ} (hM : 0 < M) (hr : 3 * M < r) :
    deriv (timePotential M L) r = 0 ↔ L ^ 2 = M * r ^ 2 / (r - 3 * M) := by
  have hr0 : r ≠ 0 := by linarith
  have hd := (timePotential_hasDerivAt (M := M) (L := L) hr0).deriv
  rw [hd]
  constructor
  · intro h
    have hnum : M * r ^ 2 - L ^ 2 * (r - 3 * M) = 0 := by
      exact (div_eq_zero_iff).mp h |>.resolve_right (pow_ne_zero 4 (by linarith))
    apply (eq_div_iff (by linarith : r - 3 * M ≠ 0)).2
    nlinarith
  · intro h
    have hbal := (eq_div_iff (by linarith : r - 3 * M ≠ 0)).mp h
    rw [hbal, sub_self, zero_div]

theorem no_circular_orbit_le_threeM {M L r : ℝ} (hM : 0 < M)
    (hr : 0 < r) (hr3 : r ≤ 3 * M) : deriv (timePotential M L) r ≠ 0 := by
  intro h
  have hd := (timePotential_hasDerivAt (M := M) (L := L) hr.ne').deriv
  rw [hd] at h
  have hnum : M * r ^ 2 = L ^ 2 * (r - 3 * M) := by
    field_simp at h
    linarith
  have hleft : 0 < M * r ^ 2 := by positivity
  have hright : L ^ 2 * (r - 3 * M) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
  linarith

theorem circular_orbit_second_deriv {M L r : ℝ} (hM : 0 < M) (hr : 3 * M < r)
    (hL : L ^ 2 = M * r ^ 2 / (r - 3 * M)) :
    deriv (deriv (timePotential M L)) r = M * (r - 6 * M) / (r ^ 3 * (r - 3 * M)) := by
  have hfirst : ∀ x : ℝ, x ≠ 0 →
      deriv (timePotential M L) x =
        (M * x ^ 2 - L ^ 2 * (x - 3 * M)) / x ^ 4 := by
    intro x hx
    exact (timePotential_hasDerivAt hx).deriv
  have hnum : HasDerivAt (fun x : ℝ => M * x ^ 2 - L ^ 2 * (x - 3 * M))
      (2 * M * r - L ^ 2) r := by
    have h := HasDerivAt.sub (HasDerivAt.const_mul M
      (HasDerivAt.pow (hasDerivAt_id r) 2))
      (HasDerivAt.const_mul (L ^ 2)
        ((hasDerivAt_id r).sub (hasDerivAt_const r (3 * M))))
    convert h using 1
    · funext x
      simp [id]
    · simp [id]
      ring
  have hden : HasDerivAt (fun x : ℝ => x ^ 4) (4 * r ^ 3) r := by
    change HasDerivAt (id ^ 4) _ r
    convert HasDerivAt.pow (hasDerivAt_id r) 4 using 1; norm_num
  have hquot := hnum.div hden (pow_ne_zero 4 (by linarith : r ≠ 0))
  have hsecond := hquot.deriv
  have hcalc : deriv (fun x : ℝ =>
      (M * x ^ 2 - L ^ 2 * (x - 3 * M)) / x ^ 4) r =
      M * (r - 6 * M) / (r ^ 3 * (r - 3 * M)) := by
    change deriv ((fun x : ℝ => M * x ^ 2 - L ^ 2 * (x - 3 * M)) /
      (fun x : ℝ => x ^ 4)) r = _
    have hdif : r - 3 * M ≠ 0 := by linarith
    have hr0 : r ≠ 0 := by linarith
    have hbal := (eq_div_iff hdif).mp hL
    rw [hsecond, hbal, sub_self, zero_mul, sub_zero, hL]
    field_simp [hdif, hr0, show r - M * 3 ≠ 0 by linarith]
    ring
  rw [show deriv (deriv (timePotential M L)) r = deriv (fun x =>
      (M * x ^ 2 - L ^ 2 * (x - 3 * M)) / x ^ 4) r by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [eventually_ne_nhds (show r ≠ 0 by linarith)] with x hx
      exact hfirst x hx]
  exact hcalc

theorem circular_orbit_stability_iff {M L r : ℝ} (hM : 0 < M) (hr : 3 * M < r)
    (hL : L ^ 2 = M * r ^ 2 / (r - 3 * M)) :
    (0 < deriv (deriv (timePotential M L)) r ↔ 6 * M < r) ∧
    (deriv (deriv (timePotential M L)) r = 0 ↔ r = 6 * M) ∧
    (deriv (deriv (timePotential M L)) r < 0 ↔ r < 6 * M) := by
  rw [circular_orbit_second_deriv hM hr hL]
  have hr0 : 0 < r := by linarith
  have hden : 0 < r ^ 3 * (r - 3 * M) :=
    mul_pos (pow_pos hr0 3) (by linarith)
  constructor
  · constructor <;> intro h
    · rcases div_pos_iff.mp h with hpos | hneg
      · nlinarith [hpos.1]
      · linarith [hneg.2, hden]
    · exact div_pos (by nlinarith) hden
  constructor
  · constructor <;> intro h
    · have hz : M * (r - 6 * M) = 0 :=
        (div_eq_zero_iff).mp h |>.resolve_right (by positivity)
      nlinarith
    · rw [h]
      simp
  · constructor <;> intro h
    · rcases div_neg_iff.mp h with hneg | hpos
      · linarith [hneg.2, hden]
      · nlinarith [hpos.1]
    · exact div_neg_of_neg_of_pos (by nlinarith) hden

theorem isco_parameters_exact {M : ℝ} (hM : 0 < M) :
    let r := 6 * M
    let L := 2 * Real.sqrt 3 * M
    L ^ 2 = 12 * M ^ 2 ∧
      2 * timePotential M L r = 8 / 9 ∧
      1 - Real.sqrt (2 * timePotential M L r) = 1 - 2 * Real.sqrt 2 / 3 := by
  dsimp
  have hs3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hM0 : M ≠ 0 := hM.ne'
  constructor
  · rw [show (2 * Real.sqrt 3 * M) ^ 2 = 4 * (Real.sqrt 3) ^ 2 * M ^ 2 by ring, hs3]
    ring
  constructor
  ·
    unfold timePotential
    field_simp [hM0]
    rw [hs3]
    ring
  ·
    have hE : 2 * timePotential M (2 * Real.sqrt 3 * M) (6 * M) = 8 / 9 := by
      unfold timePotential
      field_simp [hM0]
      rw [hs3]
      ring
    rw [hE]
    have he : (8 / 9 : ℝ) = (2 * Real.sqrt 2 / 3) ^ 2 := by
      field_simp
      rw [hs2]
      ring
    rw [show Real.sqrt (8 / 9) = 2 * Real.sqrt 2 / 3 by
      rw [he, Real.sqrt_sq_eq_abs, abs_of_pos]
      positivity]

/-- The energy of the circular family is minimized at its marginally stable radius. -/
theorem circular_orbit_energy_minimum {M L r : ℝ} (hM : 0 < M) (hr : 3 * M < r)
    (hL : L ^ 2 = M * r ^ 2 / (r - 3 * M)) :
    8 / 9 ≤ 2 * timePotential M L r ∧
      (2 * timePotential M L r = 8 / 9 ↔ r = 6 * M) := by
  have hr0 : 0 < r := by linarith
  have hgap : 0 < r - 3 * M := sub_pos.mpr hr
  have hid : 2 * timePotential M L r - 8 / 9 =
      (r - 6 * M) ^ 2 / (9 * r * (r - 3 * M)) := by
    unfold timePotential
    rw [hL]
    field_simp [hr0.ne', hgap.ne', show r - M * 3 ≠ 0 by linarith]
    ring
  have hden : 0 < 9 * r * (r - 3 * M) := by positivity
  refine ⟨sub_nonneg.mp (hid.symm ▸ div_nonneg (sq_nonneg _) hden.le), ?_⟩
  rw [← sub_eq_zero, hid, div_eq_zero_iff, or_iff_left hden.ne', sq_eq_zero_iff, sub_eq_zero]

def redshiftRatio (M r₁ r₂ : ℝ) : ℝ :=
  Real.sqrt ((1 - 2 * M / r₁) / (1 - 2 * M / r₂))

theorem schwarzschild_redshift_factor {M r₁ r₂ : ℝ} (hM : 0 < M)
    (h1 : 2 * M < r₁) (h12 : r₁ < r₂) :
    0 < redshiftRatio M r₁ r₂ ∧ redshiftRatio M r₁ r₂ < 1 := by
  unfold redshiftRatio
  have hr1 : 0 < r₁ := by linarith
  have hr2 : 0 < r₂ := by linarith
  have hden1 : 0 < 1 - 2 * M / r₁ := by
    have hlt : 2 * M / r₁ < 1 := (div_lt_one hr1).2 (by linarith)
    linarith
  have hden2 : 0 < 1 - 2 * M / r₂ := by
    have hlt : 2 * M / r₂ < 1 := (div_lt_one hr2).2 (by linarith)
    linarith
  have hlt : 1 - 2 * M / r₁ < 1 - 2 * M / r₂ := by
    have : 2 * M / r₂ < 2 * M / r₁ :=
      (div_lt_div_iff₀ hr2 hr1).2 (by nlinarith)
    linarith
  have hratio : 0 < (1 - 2 * M / r₁) / (1 - 2 * M / r₂) := div_pos hden1 hden2
  refine ⟨Real.sqrt_pos.2 hratio, ?_⟩
  apply (Real.sqrt_lt (le_of_lt hratio) zero_le_one).2
  simpa using (div_lt_one hden2).2 hlt

theorem schwarzschild_redshift_horizon_limit {M r₂ : ℝ} (hM : 0 < M) :
    Tendsto (fun r => redshiftRatio M r r₂) (𝓝[>] (2 * M)) (𝓝 0) := by
  have hnonzero : 2 * M ≠ 0 := by positivity
  have hcont : ContinuousAt (fun r : ℝ => redshiftRatio M r r₂) (2 * M) := by
    unfold redshiftRatio
    exact Real.continuous_sqrt.continuousAt.comp
      ((continuousAt_const.sub (continuousAt_const.div continuousAt_id hnonzero)).div_const _)
  have hz : redshiftRatio M (2 * M) r₂ = 0 := by
    unfold redshiftRatio
    rw [div_self hnonzero, sub_self, zero_div, Real.sqrt_zero]
  rw [← hz]
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

def u0 (b φ : ℝ) : ℝ := Real.sin φ / b
def u1 (M b φ : ℝ) : ℝ := (M / b ^ 2) * (1 + Real.cos φ ^ 2)

theorem binet_zeroth_order_ode (b φ : ℝ) :
    deriv (deriv (u0 b)) φ + u0 b φ = 0 := by
  have hder : deriv (u0 b) = fun x => Real.cos x / b := by
    funext x
    exact ((Real.hasDerivAt_sin x).div_const b).deriv
  rw [hder]
  have hcos := (Real.hasDerivAt_cos φ).div_const b
  rw [hcos.deriv]
  simp [u0]
  ring

theorem binet_first_order_ode {M b φ : ℝ} (hb : b ≠ 0) :
    deriv (deriv (u1 M b)) φ + u1 M b φ = 3 * M * (u0 b φ) ^ 2 := by
  let c : ℝ := M / b ^ 2
  have hder : deriv (u1 M b) = fun x => c * (2 * Real.cos x * (-Real.sin x)) := by
    funext x
    have hc := Real.hasDerivAt_cos x
    have hsq := HasDerivAt.mul hc hc
    have hsum := HasDerivAt.add (hasDerivAt_const x 1) hsq
    have hmul := HasDerivAt.const_mul c hsum
    change deriv (fun y : ℝ => c * (1 + Real.cos y ^ 2)) x = _
    convert hmul.deriv using 1
    · congr 1
      funext y
      simp [Pi.add_apply, Pi.mul_apply, pow_two]
    · ring
  rw [hder]
  have hs : HasDerivAt (fun x : ℝ => c * (2 * Real.cos x * (-Real.sin x)))
      (c * (2 * ((-Real.sin φ) * (-Real.sin φ) + Real.cos φ * (-Real.cos φ)))) φ := by
    have h := HasDerivAt.const_mul c
      (HasDerivAt.mul (HasDerivAt.const_mul 2 (Real.hasDerivAt_cos φ))
        (HasDerivAt.const_mul (-1) (Real.hasDerivAt_sin φ)))
    convert h using 1
    · funext x
      simp only [Pi.mul_apply]
      ring
    · ring
  rw [hs.deriv]
  dsimp [u1, u0, c]
  field_simp [hb]
  linear_combination -M * Real.sin_sq_add_cos_sq φ

theorem einstein_light_deflection_eq {M b : ℝ} (hb : b ≠ 0) :
    u1 M b 0 / (deriv (u0 b) 0) - u1 M b Real.pi /
        (deriv (u0 b) Real.pi) = 4 * M / b := by
  unfold u0 u1
  have hder : deriv (fun x : ℝ => Real.sin x / b) = fun x => Real.cos x / b := by
    funext x
    exact ((Real.hasDerivAt_sin x).div_const b).deriv
  rw [hder]
  simp
  field_simp [hb]
  ring

end D5.S3.Geometry.Lorentz.SchwarzschildOpticalGeodesics4D
