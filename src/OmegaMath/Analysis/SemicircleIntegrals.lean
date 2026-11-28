import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Omega original.

Integral identities for the semicircle profile and its endpoint singularity.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace Omega

/-- Integration by parts for the semicircle profile on a cap interval. -/
theorem semicircle_cap_integral {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    (∫ t in c..1, Real.sqrt (1 - t ^ 2)) =
      c * Real.sqrt (1 - c ^ 2) ^ 3 / 3 + (4 / 3) * ∫ t in c..1, Real.sqrt (1 - t ^ 2) ^ 3 := by
  let g : ℝ → ℝ := fun t ↦ Real.sqrt (1 - t ^ 2)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have h₄ : IntervalIntegrable (fun t ↦ 4 * g t ^ 3) volume c 1 :=
    ((hg.pow 3).const_mul 4).intervalIntegrable ..
  have h₃ : IntervalIntegrable (fun t ↦ 3 * g t) volume c 1 :=
    (hg.const_mul 3).intervalIntegrable ..
  have hprim : (∫ t in c..1, (4 * g t ^ 3 - 3 * g t)) = -(c * g c ^ 3) := by
    have hd (t : ℝ) (ht : t ∈ Ioo c 1) :
        HasDerivAt (fun t ↦ t * g t ^ 3) (4 * g t ^ 3 - 3 * g t) t := by
      have hs : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      have hh : HasDerivAt g (-t / g t) t := by
        have h := ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)).sqrt hs.ne'
        change HasDerivAt g ((0 - (2 : ℝ) * t ^ (2 - 1) * 1) / (2 * g t)) t at h
        convert h using 1
        norm_num
        ring
      have he := (hasDerivAt_id t).mul (hh.pow 3)
      convert he using 1
      all_goals try rfl
      simp only [Pi.pow_apply, id_eq, Nat.reduceSubDiff, Nat.cast_ofNat, one_mul]
      have hp : 0 < g t := Real.sqrt_pos.2 hs
      have hsq : g t ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hs.le
      calc
        _ = g t ^ 3 - 3 * t ^ 2 * g t := by linear_combination 3 * g t * hsq
        _ = _ := by field_simp; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc₁
      (continuous_id.mul (hg.pow 3)).continuousOn hd
      (h₄.sub h₃)]
    norm_num [g]
  change (∫ t in c..1, g t) = c * g c ^ 3 / 3 + (4 / 3) * ∫ t in c..1, g t ^ 3
  rw [intervalIntegral.integral_sub h₄ h₃, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hprim
  linarith

/-- The semicircle density divided by distance to its right endpoint has integral π. -/
theorem semicircle_div_one_sub :
    IntegrableOn (fun x : ℝ ↦ Real.sqrt (1 - x ^ 2) / (1 - x)) (Icc (-1) 1) ∧
      (∫ x in Icc (-1 : ℝ) 1, Real.sqrt (1 - x ^ 2) / (1 - x)) = Real.pi := by
  simp only [IntegrableOn, ← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)))]
  let s := Ioo (-(Real.pi / 2)) (Real.pi / 2)
  have hsin : Real.sin '' s = Ioo (-1 : ℝ) 1 := by
    exact Real.sinPartialHomeomorph.toPartialEquiv.image_source_eq_target
  have hd (t : ℝ) (_ : t ∈ s) : HasDerivWithinAt Real.sin (Real.cos t) s t :=
    (Real.hasDerivAt_sin t).hasDerivWithinAt
  have hi : InjOn Real.sin s := Real.injOn_sin.mono Ioo_subset_Icc_self
  change IntegrableOn (fun x : ℝ ↦ Real.sqrt (1 - x ^ 2) / (1 - x)) (Ioo (-1) 1) ∧
    (∫ x in Ioo (-1 : ℝ) 1, Real.sqrt (1 - x ^ 2) / (1 - x)) = Real.pi
  have hs : MeasurableSet s := measurableSet_Ioo
  rw [← hsin, integrableOn_image_iff_integrableOn_abs_deriv_smul hs hd hi,
    integral_image_eq_integral_abs_deriv_smul hs hd hi]
  have heq (t : ℝ) (ht : t ∈ s) :
      |Real.cos t| • (Real.sqrt (1 - Real.sin t ^ 2) / (1 - Real.sin t)) = 1 + Real.sin t := by
    have hcos := Real.cos_pos_of_mem_Ioo ht
    have hsin := (Real.mapsTo_sin_Ioo ht).2.ne
    have hsq : 1 - Real.sin t ^ 2 = Real.cos t ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq t]
    rw [abs_of_pos hcos, hsq, Real.sqrt_sq hcos.le, smul_eq_mul]
    field_simp [show 1 - Real.sin t ≠ 0 by exact sub_ne_zero.mpr hsin.symm]
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [integrableOn_congr_fun heq hs, setIntegral_congr_fun hs heq,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] :
      -(Real.pi / 2) ≤ Real.pi / 2)]
  have h₁ : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume (-(Real.pi / 2)) (Real.pi / 2) :=
    intervalIntegrable_const
  have h₂ : IntervalIntegrable Real.sin volume (-(Real.pi / 2)) (Real.pi / 2) :=
    Real.continuous_sin.intervalIntegrable ..
  refine ⟨(h₁.add h₂).1.mono_set Ioo_subset_Ioc_self, ?_⟩
  rw [intervalIntegral.integral_add h₁ h₂, intervalIntegral.integral_const, integral_sin]
  simp [Real.cos_pi_div_two]

end Omega
