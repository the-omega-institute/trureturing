/- GID: D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: FLRW conservation, exact power-law and dust-vacuum solutions, and conformal horizons. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact FLRW equations in units with light speed one. Cosmological time and the
scale factor are positive on the solution branches used below. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Geometry.Lorentz.FLRWCosmologyFriedmann4D

private theorem first_integral_deriv {a v ρ : ℝ → ℝ} {t b r G Λ p : ℝ}
    (ha : HasDerivAt a (v t) t) (hv : HasDerivAt v b t) (hρ : HasDerivAt ρ r t)
    (ha0 : 0 < a t)
    (hII : b / a t = -(4 * Real.pi * G / 3) * (ρ t + 3 * p) + Λ / 3) :
    HasDerivAt (fun s => v s ^ 2 - (8 * Real.pi * G / 3) * ρ s * a s ^ 2 -
      Λ / 3 * a s ^ 2)
      (-(8 * Real.pi * G / 3) * (a t)^2 * (r + 3 * (v t / a t) * (ρ t + p))) t := by
  have hb := (div_eq_iff ha0.ne').mp hII
  have hd := ((hv.pow 2).sub ((hρ.const_mul (8 * Real.pi * G / 3)).mul (ha.pow 2))).sub
    ((ha.pow 2).const_mul (Λ / 3))
  convert hd using 1
  rw [hb]
  simp only [Pi.pow_apply]
  field_simp [ha0.ne']
  ring

theorem friedmann_implies_continuity {a v ρ p : ℝ → ℝ} {t b r G k Λ : ℝ}
    (ha0 : 0 < a t) (hG : 0 < G) (ha : HasDerivAt a (v t) t)
    (hv : HasDerivAt v b t) (hρ : HasDerivAt ρ r t)
    (hI : ∀ᶠ s in 𝓝 t, v s ^ 2 + k = (8 * Real.pi * G / 3) * ρ s * a s ^ 2 +
      Λ / 3 * a s ^ 2)
    (hII : b / a t = -(4 * Real.pi * G / 3) * (ρ t + 3 * p t) + Λ / 3) :
    r + 3 * (v t / a t) * (ρ t + p t) = 0 := by
  have hc : HasDerivAt (fun s => v s ^ 2 - (8 * Real.pi * G / 3) * ρ s * a s ^ 2 -
      Λ / 3 * a s ^ 2) 0 t :=
    (hasDerivAt_const t (-k)).congr_of_eventuallyEq <| hI.mono fun s hs => by linarith
  have hz := (first_integral_deriv ha hv hρ ha0 hII).unique hc
  have hcoef : 0 < (8 * Real.pi * G / 3) * (a t) ^ 2 := by positivity
  rw [neg_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr hcoef.ne')

theorem continuity_and_friedmann_II_conserve_first_integral
    {a v ρ p : ℝ → ℝ} {t b r G Λ : ℝ}
    (ha0 : 0 < a t) (ha : HasDerivAt a (v t) t)
    (hv : HasDerivAt v b t) (hρ : HasDerivAt ρ r t)
    (hII : b / a t = -(4 * Real.pi * G / 3) * (ρ t + 3 * p t) + Λ / 3)
    (hc : r + 3 * (v t / a t) * (ρ t + p t) = 0) :
    HasDerivAt (fun s => v s ^ 2 - (8 * Real.pi * G / 3) * ρ s * a s ^ 2 -
      Λ / 3 * a s ^ 2) 0 t := by
  simpa only [hc, mul_zero] using first_integral_deriv ha hv hρ ha0 hII

/-- Density at scale factor a, normalized at a₀, for constant pressure ratio w. -/
def eosDensity (ρ₀ a₀ w a : ℝ) : ℝ := ρ₀ * (a / a₀) ^ (-(3 * (1 + w)))

theorem eosDensity_continuity_ode {a : ℝ → ℝ} {t v ρ₀ a₀ w : ℝ}
    (ha : HasDerivAt a v t) (hat : 0 < a t) (ha₀ : 0 < a₀) :
    HasDerivAt (fun s => eosDensity ρ₀ a₀ w (a s))
      (-(3 * (v / a t) * (1 + w) * eosDensity ρ₀ a₀ w (a t))) t := by
  let n := -(3 * (1 + w))
  have hbase := div_pos hat ha₀
  have hd := ((ha.div_const a₀).rpow_const (p := n) (Or.inl hbase.ne')).const_mul ρ₀
  convert hd using 1
  · rfl
  change -(3 * (v / a t) * (1 + w) * (ρ₀ * (a t / a₀) ^ n)) =
    ρ₀ * (v / a₀ * n * (a t / a₀) ^ (n - 1))
  rw [Real.rpow_sub hbase, Real.rpow_one]
  dsimp [n]
  field_simp [ha₀.ne', hat.ne']

theorem eosDensity_dust_radiation_vacuum {ρ₀ a₀ a : ℝ} (h : 0 ≤ a / a₀) :
    eosDensity ρ₀ a₀ 0 a = ρ₀ / (a / a₀) ^ 3 ∧
    eosDensity ρ₀ a₀ (1 / 3) a = ρ₀ / (a / a₀) ^ 4 ∧
    eosDensity ρ₀ a₀ (-1) a = ρ₀ := by
  have h₃ : -(3 * (1 + (0 : ℝ))) = -(3 : ℝ) := by norm_num
  have h₄ : -(3 * (1 + (1 / 3 : ℝ))) = -(4 : ℝ) := by norm_num
  have h₀ : -(3 * (1 + (-1 : ℝ))) = 0 := by norm_num
  simp only [eosDensity, h₃, h₄, h₀, Real.rpow_neg h, Real.rpow_ofNat, Real.rpow_zero,
    ← div_eq_mul_inv, mul_one, and_self]

theorem acceleration_iff_strong_energy_violation {a b G ρ w : ℝ}
    (ha : 0 < a) (hG : 0 < G) (hρ : 0 < ρ)
    (hII : b / a = -(4 * Real.pi * G / 3) * (ρ + 3 * (w * ρ))) :
    0 < b ↔ w < -1 / 3 := by
  have hcoef : 0 < (4 * Real.pi * G / 3) * ρ := by positivity
  have hb := (div_eq_iff ha.ne').mp hII
  rw [hb, mul_pos_iff_of_pos_right ha]
  rw [show -(4 * Real.pi * G / 3) * (ρ + 3 * (w * ρ)) =
    ((4 * Real.pi * G / 3) * ρ) * (-(1 + 3 * w)) by ring, mul_pos_iff_of_pos_left hcoef]
  constructor <;> intro h <;> linarith

theorem dust_acceleration_iff {a b G ρ Λ : ℝ} (ha : 0 < a)
    (hII : b / a = -(4 * Real.pi * G / 3) * ρ + Λ / 3) :
    0 < b ↔ (4 * Real.pi * G) * ρ < Λ := by
  rw [(div_eq_iff ha.ne').mp hII, mul_pos_iff_of_pos_right ha]
  constructor <;> intro h <;> linarith

def flatExponent (w : ℝ) : ℝ := 2 / (3 * (1 + w))
def flatScaleFactor (a₁ α t : ℝ) : ℝ := a₁ * t ^ α
def flatDensity (G w t : ℝ) : ℝ := 1 / (6 * Real.pi * G * (1 + w)^2 * t^2)

def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t
def deceleration (a : ℝ → ℝ) (t : ℝ) : ℝ := -(a t * deriv (deriv a) t) / deriv a t ^ 2

private theorem flatExponent_pos {w : ℝ} (hw : -1 < w) : 0 < flatExponent w := by
  unfold flatExponent
  have : 0 < 1 + w := by linarith
  positivity

private theorem flat_deriv {a₁ α t : ℝ} (ht : 0 < t) :
    HasDerivAt (flatScaleFactor a₁ α) (a₁ * (α * t ^ (α - 1))) t :=
  (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul a₁

private theorem flat_hubble_and_acceleration {a₁ α t : ℝ} (ha₁ : 0 < a₁) (ht : 0 < t) :
    hubble (flatScaleFactor a₁ α) t = α / t ∧
    deriv (deriv (flatScaleFactor a₁ α)) t / flatScaleFactor a₁ α t =
      α * (α - 1) / t ^ 2 := by
  have hpow : 0 < t ^ α := Real.rpow_pos_of_pos ht _
  have hd' : HasDerivAt (deriv (flatScaleFactor a₁ α))
      (a₁ * (α * ((α - 1) * t ^ (α - 1 - 1)))) t :=
    (((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul α).const_mul a₁)
      |>.congr_of_eventuallyEq ((eventually_gt_nhds ht).mono fun _ hs => (flat_deriv hs).deriv)
  constructor
  · rw [hubble, (flat_deriv ht).deriv, flatScaleFactor, Real.rpow_sub ht, Real.rpow_one]
    field_simp [ha₁.ne', ht.ne', hpow.ne']
  · rw [hd'.deriv, flatScaleFactor, Real.rpow_sub ht, Real.rpow_sub ht, Real.rpow_one]
    field_simp [ha₁.ne', ht.ne', hpow.ne']

theorem flat_power_law_satisfies_friedmann {a₁ G w t : ℝ} (ha₁ : 0 < a₁) (hG : 0 < G)
    (hw : -1 < w) (ht : 0 < t) :
    hubble (flatScaleFactor a₁ (flatExponent w)) t ^ 2 =
      (8 * Real.pi * G / 3) * flatDensity G w t ∧
    deriv (deriv (flatScaleFactor a₁ (flatExponent w))) t / flatScaleFactor a₁ (flatExponent w) t =
      -(4 * Real.pi * G / 3) * (1 + 3 * w) * flatDensity G w t := by
  obtain ⟨hH, hb⟩ := flat_hubble_and_acceleration (α := flatExponent w) ha₁ ht
  rw [hH, hb]
  have hw' : (1 + w) ≠ 0 := ne_of_gt (by linarith)
  constructor <;> unfold flatExponent flatDensity <;>
    field_simp [hG.ne', ht.ne', hw', Real.pi_ne_zero] <;> ring

theorem flat_power_law_hubble_age {a₁ w t : ℝ} (ha₁ : 0 < a₁) (ht : 0 < t) :
    hubble (flatScaleFactor a₁ (flatExponent w)) t * t = 2 / (3 * (1 + w)) := by
  rw [(flat_hubble_and_acceleration ha₁ ht).1, div_mul_cancel₀ _ ht.ne']
  rfl

theorem flat_dust_radiation_age {a₁ t : ℝ} (ha₁ : 0 < a₁) (ht : 0 < t) :
    t = 2 / (3 * hubble (flatScaleFactor a₁ (flatExponent 0)) t) ∧
    t = 1 / (2 * hubble (flatScaleFactor a₁ (flatExponent (1 / 3))) t) := by
  rw [(flat_hubble_and_acceleration ha₁ ht).1, (flat_hubble_and_acceleration ha₁ ht).1]
  constructor <;> norm_num [flatExponent]
  field_simp [ht.ne']

theorem flat_power_law_deceleration {a₁ w t : ℝ} (ha₁ : 0 < a₁) (hw : -1 < w)
    (ht : 0 < t) :
    deceleration (flatScaleFactor a₁ (flatExponent w)) t = (1 + 3 * w) / 2 := by
  let α := flatExponent w
  let a := flatScaleFactor a₁ α
  have ha : 0 < a t := mul_pos ha₁ (Real.rpow_pos_of_pos ht _)
  have hα : 0 < α := flatExponent_pos hw
  obtain ⟨hH, hb⟩ := flat_hubble_and_acceleration (α := α) ha₁ ht
  have hv : deriv a t = (α / t) * a t := (div_eq_iff ha.ne').mp hH
  have hacc : deriv (deriv a) t = (α * (α - 1) / t ^ 2) * a t := (div_eq_iff ha.ne').mp hb
  change deceleration a t = _
  rw [deceleration, hv, hacc]
  calc
    _ = (1 - α) / α := by field_simp [ha.ne', ht.ne', hα.ne']; ring
    _ = _ := by
      have hw' : (1 + w) ≠ 0 := ne_of_gt (by linarith)
      dsimp [α, flatExponent]
      field_simp [hw']
      ring

theorem flat_deceleration_thresholds {a₁ w t : ℝ} (ha₁ : 0 < a₁) (hw : -1 < w)
    (ht : 0 < t) :
    deceleration (flatScaleFactor a₁ (flatExponent 0)) t = 1 / 2 ∧
    deceleration (flatScaleFactor a₁ (flatExponent (1 / 3))) t = 1 ∧
    (deceleration (flatScaleFactor a₁ (flatExponent w)) t < 0 ↔ w < -1 / 3) := by
  rw [flat_power_law_deceleration ha₁ hw ht,
    flat_power_law_deceleration ha₁ (by norm_num : (-1 : ℝ) < 0) ht,
    flat_power_law_deceleration ha₁ (by norm_num : (-1 : ℝ) < 1 / 3) ht]
  norm_num
  constructor <;> intro h <;> linarith

private def lcdmArgument (H t : ℝ) : ℝ := (3 / 2 : ℝ) * H * t

def lcdmScaleFactor (aStar H t : ℝ) : ℝ :=
  aStar * (Real.sinh (lcdmArgument H t)) ^ (2 / 3 : ℝ)

def lcdmDensity (aStar H G t : ℝ) : ℝ :=
  (H ^ 2 * (aStar / lcdmScaleFactor aStar H t) ^ 3) / (8 * Real.pi * G / 3)

private theorem lcdm_sinh_pos {H t : ℝ} (hH : 0 < H) (ht : 0 < t) :
    0 < Real.sinh (lcdmArgument H t) := Real.sinh_pos_iff.mpr (by
  unfold lcdmArgument
  positivity)

private theorem lcdmScaleFactor_pos {aStar H t : ℝ} (ha : 0 < aStar) (hH : 0 < H) (ht : 0 < t) :
    0 < lcdmScaleFactor aStar H t := mul_pos ha (Real.rpow_pos_of_pos (lcdm_sinh_pos hH ht) _)

private theorem lcdmArgument_hasDerivAt (H t : ℝ) :
    HasDerivAt (lcdmArgument H) ((3 / 2 : ℝ) * H) t :=
  hasDerivAt_const_mul ((3 / 2 : ℝ) * H)

private theorem lcdm_sinh_hasDerivAt (H t : ℝ) :
    HasDerivAt (fun s => Real.sinh (lcdmArgument H s))
      (Real.cosh (lcdmArgument H t) * ((3 / 2 : ℝ) * H)) t :=
  (Real.hasDerivAt_sinh _).comp t (lcdmArgument_hasDerivAt H t)

private theorem lcdm_cosh_hasDerivAt (H t : ℝ) :
    HasDerivAt (fun s => Real.cosh (lcdmArgument H s))
      (Real.sinh (lcdmArgument H t) * ((3 / 2 : ℝ) * H)) t :=
  (Real.hasDerivAt_cosh _).comp t (lcdmArgument_hasDerivAt H t)

private theorem lcdm_hasDerivAt (aStar : ℝ) {H t : ℝ} (hH : 0 < H) (ht : 0 < t) :
    HasDerivAt (lcdmScaleFactor aStar H)
      (lcdmScaleFactor aStar H t * (H * Real.cosh (lcdmArgument H t) /
        Real.sinh (lcdmArgument H t))) t := by
  have hs := lcdm_sinh_pos hH ht
  have hd := ((lcdm_sinh_hasDerivAt H t).rpow_const (p := (2 / 3 : ℝ))
    (Or.inl hs.ne')).const_mul aStar
  convert hd using 1
  · rfl
  let S := Real.sinh (lcdmArgument H t)
  let C := Real.cosh (lcdmArgument H t)
  change aStar * S ^ (2 / 3 : ℝ) * (H * C / S) =
    aStar * (C * (3 / 2 * H) * (2 / 3 : ℝ) * S ^ ((2 / 3 : ℝ) - 1))
  rw [Real.rpow_sub hs, Real.rpow_one]
  ring

theorem lcdm_hubble_eq {aStar H t : ℝ} (ha : 0 < aStar) (hH : 0 < H) (ht : 0 < t) :
    hubble (lcdmScaleFactor aStar H) t =
      H * Real.cosh ((3 / 2 : ℝ) * H * t) / Real.sinh ((3 / 2 : ℝ) * H * t) := by
  change _ = H * Real.cosh (lcdmArgument H t) / Real.sinh (lcdmArgument H t)
  rw [hubble, (lcdm_hasDerivAt aStar hH ht).deriv,
    mul_div_cancel_left₀ _ (lcdmScaleFactor_pos ha hH ht).ne']

private theorem lcdm_scale_ratio_cube {aStar H t : ℝ} (hH : 0 < H) (ht : 0 < t)
    (ha : aStar ≠ 0) :
    (lcdmScaleFactor aStar H t / aStar) ^ 3 = Real.sinh (lcdmArgument H t) ^ 2 := by
  rw [lcdmScaleFactor, mul_div_cancel_left₀ _ ha, ← Real.rpow_natCast,
    ← Real.rpow_mul (lcdm_sinh_pos hH ht).le]
  norm_num [Real.rpow_ofNat]

private theorem lcdm_inverse_ratio_cube {aStar H t : ℝ} (ha : 0 < aStar) (hH : 0 < H)
    (ht : 0 < t) : (aStar / lcdmScaleFactor aStar H t) ^ 3 =
      1 / Real.sinh (lcdmArgument H t) ^ 2 := by
  rw [← inv_div, inv_pow, lcdm_scale_ratio_cube hH ht ha.ne', one_div]

private theorem lcdm_normalized_density {aStar H G t : ℝ} (hG : 0 < G) :
    (8 * Real.pi * G / 3) * lcdmDensity aStar H G t =
      H ^ 2 * (aStar / lcdmScaleFactor aStar H t) ^ 3 := by
  unfold lcdmDensity
  have h : (8 * Real.pi * G / 3) ≠ 0 := ne_of_gt (by positivity)
  exact mul_div_cancel₀ _ h

private theorem lcdm_acceleration_ratio {aStar H t : ℝ} (ha : 0 < aStar) (hH : 0 < H)
    (ht : 0 < t) :
    deriv (deriv (lcdmScaleFactor aStar H)) t / lcdmScaleFactor aStar H t =
      H ^ 2 - H ^ 2 / (2 * Real.sinh (lcdmArgument H t) ^ 2) := by
  let S := Real.sinh (lcdmArgument H t)
  let C := Real.cosh (lcdmArgument H t)
  let a := lcdmScaleFactor aStar H
  have hs : 0 < S := lcdm_sinh_pos hH ht
  have ha' : 0 < a t := lcdmScaleFactor_pos ha hH ht
  have hC : C ^ 2 - S ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
  have hquot := ((lcdm_cosh_hasDerivAt H t).const_mul H).div (lcdm_sinh_hasDerivAt H t) hs.ne'
  have hd := ((lcdm_hasDerivAt aStar hH ht).mul hquot).congr_of_eventuallyEq
    ((eventually_gt_nhds ht).mono fun _ hu => (lcdm_hasDerivAt aStar hH hu).deriv)
  rw [hd.deriv]
  change (a t * (H * C / S) * (H * C / S) +
    a t * ((H * (S * (3 / 2 * H)) * S - H * C * (C * (3 / 2 * H))) / S ^ 2)) / a t = _
  change _ = H ^ 2 - H ^ 2 / (2 * S ^ 2)
  field_simp [ha'.ne', hs.ne']
  linear_combination -hC

theorem lcdm_satisfies_friedmann_I {aStar H G t : ℝ} (ha : 0 < aStar) (hH : 0 < H)
    (hG : 0 < G) (ht : 0 < t) :
    hubble (lcdmScaleFactor aStar H) t ^ 2 =
      (8 * Real.pi * G / 3) * lcdmDensity aStar H G t + H ^ 2 := by
  rw [lcdm_hubble_eq ha hH ht, lcdm_normalized_density hG, lcdm_inverse_ratio_cube ha hH ht]
  let S := Real.sinh (lcdmArgument H t)
  let C := Real.cosh (lcdmArgument H t)
  have hC : C ^ 2 - S ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
  change (H * C / S) ^ 2 = H ^ 2 * (1 / S ^ 2) + H ^ 2
  have hs : 0 < S := lcdm_sinh_pos hH ht
  field_simp [hs.ne']
  linear_combination hC

theorem lcdm_satisfies_friedmann_II {aStar H G t : ℝ} (ha : 0 < aStar) (hH : 0 < H)
    (hG : 0 < G) (ht : 0 < t) :
    deriv (deriv (lcdmScaleFactor aStar H)) t / lcdmScaleFactor aStar H t =
      -(4 * Real.pi * G / 3) * lcdmDensity aStar H G t + H ^ 2 := by
  rw [lcdm_acceleration_ratio ha hH ht]
  have h := lcdm_normalized_density (aStar := aStar) (H := H) (t := t) hG
  rw [lcdm_inverse_ratio_cube ha hH ht] at h
  let S := Real.sinh (lcdmArgument H t)
  change (8 * Real.pi * G / 3) * lcdmDensity aStar H G t = H ^ 2 * (1 / S ^ 2) at h
  change H ^ 2 - H ^ 2 / (2 * S ^ 2) = -(4 * Real.pi * G / 3) * lcdmDensity aStar H G t + H ^ 2
  linear_combination h / 2

theorem lcdm_inflection_iff {aStar H t : ℝ} (ha : 0 < aStar) (hH : 0 < H) (ht : 0 < t) :
    0 < deriv (deriv (lcdmScaleFactor aStar H)) t ↔
      1 / Real.sqrt 2 < Real.sinh ((3 / 2 : ℝ) * H * t) := by
  let S := Real.sinh (lcdmArgument H t)
  have hs : 0 < S := lcdm_sinh_pos hH ht
  have ha' := lcdmScaleFactor_pos ha hH ht
  have h₂ : 0 < Real.sqrt 2 := by positivity
  have hsq : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hden : 0 < 2 * S ^ 2 := by positivity
  have hH2 : 0 < H ^ 2 := by positivity
  rw [← div_pos_iff_of_pos_right ha', lcdm_acceleration_ratio ha hH ht, sub_pos,
    div_lt_iff₀ hden]
  change H ^ 2 < H ^ 2 * (2 * S ^ 2) ↔ 1 / Real.sqrt 2 < S
  have hmul : H ^ 2 < H ^ 2 * (2 * S ^ 2) ↔ 1 < 2 * S ^ 2 := by
    simpa only [mul_one] using mul_lt_mul_iff_right₀ hH2 (b := 1) (c := 2 * S ^ 2)
  have hsquares := sq_lt_sq₀ (by positivity : 0 ≤ 1 / Real.sqrt 2) hs.le
  rw [hmul, ← hsquares, hsq]
  constructor <;> intro h <;> linarith

theorem lcdm_density_parameter_acceleration {aStar H G t : ℝ} (ha : 0 < aStar)
    (hH : 0 < H) (hG : 0 < G) (ht : 0 < t) :
    let Ht := hubble (lcdmScaleFactor aStar H) t
    let Ωm := ((8 * Real.pi * G / 3) * lcdmDensity aStar H G t) / Ht ^ 2
    let ΩΛ := H ^ 2 / Ht ^ 2
    0 < deriv (deriv (lcdmScaleFactor aStar H)) t ↔ Ωm < 2 * ΩΛ := by
  dsimp only
  have hHt : 0 < hubble (lcdmScaleFactor aStar H) t := by
    rw [lcdm_hubble_eq ha hH ht]
    exact div_pos (mul_pos hH (Real.cosh_pos _)) (lcdm_sinh_pos hH ht)
  have hII := lcdm_satisfies_friedmann_II ha hH hG ht
  rw [← div_pos_iff_of_pos_right (lcdmScaleFactor_pos ha hH ht), hII, ← mul_div_assoc,
    div_lt_div_iff_of_pos_right (sq_pos_of_pos hHt)]
  constructor <;> intro h <;> linarith

/-- Matter-to-vacuum density ratio for the flat dust and vacuum solution. -/
def lcdmMatterVacuumRatio (aStar H t : ℝ) : ℝ := (aStar / lcdmScaleFactor aStar H t) ^ 3

private theorem lcdm_acceleration_zero_iff {aStar H t : ℝ} (ha : 0 < aStar) (hH : 0 < H)
    (ht : 0 < t) :
    deriv (deriv (lcdmScaleFactor aStar H)) t = 0 ↔
      Real.sinh (lcdmArgument H t) ^ 2 = 1 / 2 := by
  let S := Real.sinh (lcdmArgument H t)
  let a := lcdmScaleFactor aStar H
  have hs : 0 < S := lcdm_sinh_pos hH ht
  have ha' := lcdmScaleFactor_pos ha hH ht
  have hH2 : H ^ 2 ≠ 0 := pow_ne_zero _ hH.ne'
  have hden : 2 * S ^ 2 ≠ 0 := by positivity
  have hnorm := lcdm_acceleration_ratio ha hH ht
  change deriv (deriv a) t / a t = H ^ 2 - H ^ 2 / (2 * S ^ 2) at hnorm
  have hzero : deriv (deriv a) t / a t = 0 ↔ deriv (deriv a) t = 0 :=
    div_eq_zero_iff.trans (or_iff_left ha'.ne')
  change deriv (deriv a) t = 0 ↔ S ^ 2 = 1 / 2
  rw [← hzero, hnorm, sub_eq_zero, eq_div_iff hden]
  constructor
  · intro h
    have h' : 2 * S ^ 2 = 1 := mul_left_cancel₀ hH2 (h.trans (mul_one _).symm)
    linarith
  · intro h
    rw [h]
    ring

private theorem transition_ratio_cube : ((2 : ℝ) ^ (-(1 / 3 : ℝ))) ^ 3 = 1 / 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [Real.rpow_neg_one]

theorem lcdm_transition_scale {aStar H t : ℝ} (ha : 0 < aStar) (hH : 0 < H) (ht : 0 < t) :
    deriv (deriv (lcdmScaleFactor aStar H)) t = 0 ↔
      lcdmScaleFactor aStar H t / aStar = (2 : ℝ) ^ (-(1 / 3 : ℝ)) := by
  rw [lcdm_acceleration_zero_iff ha hH ht]
  rw [← pow_left_inj₀ (div_pos (lcdmScaleFactor_pos ha hH ht) ha).le
    (Real.rpow_nonneg (by norm_num) _) (by decide : 3 ≠ 0),
    lcdm_scale_ratio_cube hH ht ha.ne', transition_ratio_cube]

theorem lcdm_transition_time {aStar H : ℝ} (ha : 0 < aStar) (hH : 0 < H) :
    let tAcc := Real.arsinh (1 / Real.sqrt 2) / ((3 / 2 : ℝ) * H)
    0 < tAcc ∧ ∀ t : ℝ, 0 < t →
      (deriv (deriv (lcdmScaleFactor aStar H)) t = 0 ↔ t = tAcc) := by
  let u := 1 / Real.sqrt 2
  let k := (3 / 2 : ℝ) * H
  have hu : 0 < u := by unfold u; positivity
  have hk : 0 < k := by unfold k; positivity
  have hu2 : u ^ 2 = 1 / 2 := by
    unfold u
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  change 0 < Real.arsinh u / k ∧ _
  refine ⟨div_pos (Real.arsinh_pos_iff.mpr hu) hk, fun t ht => ?_⟩
  change deriv (deriv (lcdmScaleFactor aStar H)) t = 0 ↔ t = Real.arsinh u / k
  have hs : Real.sinh (lcdmArgument H t) = u ↔ lcdmArgument H t = Real.arsinh u :=
    ⟨fun h => Real.sinh_injective (h.trans (Real.sinh_arsinh u).symm), fun h => by
      rw [h, Real.sinh_arsinh]⟩
  rw [lcdm_acceleration_zero_iff ha hH ht, ← hu2,
    sq_eq_sq₀ (lcdm_sinh_pos hH ht).le hu.le, hs, eq_div_iff hk.ne']
  change k * t = Real.arsinh u ↔ t * k = Real.arsinh u
  rw [mul_comm k t]

theorem lcdm_transition_redshift {aStar H t₀ tAcc : ℝ} (ha : 0 < aStar) (hH : 0 < H)
    (ht₀ : 0 < t₀) (htAcc : 0 < tAcc)
    (hacc : deriv (deriv (lcdmScaleFactor aStar H)) tAcc = 0) :
    (lcdmScaleFactor aStar H t₀ / lcdmScaleFactor aStar H tAcc) ^ 3 =
      2 / lcdmMatterVacuumRatio aStar H t₀ := by
  let a := lcdmScaleFactor aStar H
  have ha₀ : 0 < a t₀ := lcdmScaleFactor_pos ha hH ht₀
  have hscale := (lcdm_transition_scale ha hH htAcc).mp hacc
  have hc := congrArg (fun x : ℝ => x ^ (3 : ℕ)) hscale
  change (a tAcc / aStar) ^ 3 = _ at hc
  rw [transition_ratio_cube, div_pow] at hc
  have hAcc := (div_eq_iff (pow_ne_zero 3 ha.ne')).mp hc
  change (a t₀ / a tAcc) ^ 3 = 2 / (aStar / a t₀) ^ 3
  rw [div_pow, div_pow, hAcc]
  field_simp [ha.ne', ha₀.ne']

theorem lcdm_hubble_tendsto_desitter {aStar H : ℝ} (ha : 0 < aStar) (hH : 0 < H) :
    Tendsto (hubble (lcdmScaleFactor aStar H)) atTop (𝓝 H) := by
  have huv : Tendsto (fun t : ℝ => -(2 * lcdmArgument H t)) atTop atBot := by
    have h : -(2 * ((3 / 2 : ℝ) * H)) < 0 := by linarith
    convert (tendsto_id.const_mul_atTop_of_neg h) using 1
    ext t
    simp only [lcdmArgument, id_eq]
    ring
  have he := Real.tendsto_exp_atBot.comp huv
  have hOne : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hplus := hOne.add he
  have hminus := hOne.sub he
  have h := (hplus.div hminus (by norm_num)).const_mul H
  simp only [add_zero, sub_zero, div_one, mul_one] at h
  refine h.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun t ht => ?_)
  rw [lcdm_hubble_eq ha hH ht]
  let x := lcdmArgument H t
  change H * ((1 + Real.exp (-(2 * x))) / (1 - Real.exp (-(2 * x)))) =
    H * Real.cosh x / Real.sinh x
  have hs : Real.sinh x ≠ 0 := (lcdm_sinh_pos hH ht).ne'
  have hx : 0 < x := by unfold x lcdmArgument; positivity
  have hden : 1 - Real.exp (-(2 * x)) ≠ 0 := ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have heq : Real.exp (-(2 * x)) = (Real.exp x)⁻¹ ^ 2 := by
    rw [show -(2 * x) = -(x + x) by ring, Real.exp_neg, Real.exp_add, mul_inv, pow_two]
  have hd : Real.exp x - (Real.exp x)⁻¹ ≠ 0 := by
    intro h'
    apply hs
    rw [Real.sinh_eq, Real.exp_neg, h', zero_div]
  rw [heq, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  rw [heq] at hden
  field_simp [hden, hd, Real.exp_ne_zero]

theorem particle_horizon_finite_iff {α T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioc 0 T) ↔ α < 1 := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le,
    intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le,
    intervalIntegral.integrableOn_Ioo_rpow_iff hT]
  constructor <;> intro h <;> linarith

theorem event_horizon_finite_iff {α T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioi T) ↔ 1 < α := by
  rw [integrableOn_Ioi_rpow_iff hT]
  constructor <;> intro h <;> linarith

theorem particle_horizon_integral {α T : ℝ} (hT : 0 < T) (hα : α < 1) :
    ∫ t : ℝ in Ioc 0 T, t ^ (-α) = T ^ (1 - α) / (1 - α) := by
  rw [← intervalIntegral.integral_of_le hT.le,
    integral_rpow (Or.inl (by linarith : -1 < -α)),
    show -α + 1 = 1 - α by ring, Real.zero_rpow (by linarith : 1 - α ≠ 0), sub_zero]

theorem event_horizon_integral {α T : ℝ} (hT : 0 < T) (hα : 1 < α) :
    ∫ t : ℝ in Ioi T, t ^ (-α) = T ^ (1 - α) / (α - 1) := by
  rw [integral_Ioi_rpow_of_lt (by linarith : -α < -1) hT, show -α + 1 = 1 - α by ring,
    neg_div, ← div_neg_eq_neg_div, neg_sub]

theorem flat_horizon_thresholds {T w : ℝ} (hT : 0 < T) (hw : -1 < w) :
    (IntegrableOn (fun t : ℝ => t ^ (-flatExponent w)) (Ioc 0 T) ↔ -1 / 3 < w) ∧
    (IntegrableOn (fun t : ℝ => t ^ (-flatExponent w)) (Ioi T) ↔ w < -1 / 3) := by
  have h : 0 < 3 * (1 + w) := by linarith
  rw [particle_horizon_finite_iff hT, event_horizon_finite_iff hT, flatExponent,
    div_lt_iff₀ h, lt_div_iff₀ h]
  exact ⟨⟨fun h => by linarith, fun h => by linarith⟩,
    ⟨fun h => by linarith, fun h => by linarith⟩⟩

end D5.S3.Geometry.Lorentz.FLRWCosmologyFriedmann4D
