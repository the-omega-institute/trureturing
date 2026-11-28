/- GID: D5/S3/Analysis/SingularSecondOrder
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-schwinger4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniqueness for the second-order equation `t f''(t) = f(t)` with zero right-hand limits of the solution and its first derivative. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Omega original.

Uniqueness for the second-order equation `t f''(t) = f(t)` with zero
right-hand limits of the solution and its first derivative.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Topology

namespace Omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem norm_le_mul_of_hasDerivAt_of_tendsto_zero
    {f g : ℝ → E} {r bound : ℝ}
    (hf : ∀ x ∈ Ioc 0 r, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Ioc 0 r, ‖g x‖ ≤ bound)
    (hf₀ : Tendsto f (𝓝[>] 0) (𝓝 0))
    {t : ℝ} (ht : t ∈ Ioc 0 r) : ‖f t‖ ≤ bound * t := by
  have hslope : ∀ᶠ a in 𝓝[>] (0 : ℝ), ‖f t - f a‖ ≤ bound * (t - a) := by
    filter_upwards [Ioo_mem_nhdsGT ht.1] with a ha
    have hIcc : Icc a t ⊆ Ioc 0 r :=
      fun _ hx => ⟨ha.1.trans_le hx.1, hx.2.trans ht.2⟩
    apply norm_image_sub_le_of_norm_deriv_right_le_segment
      (fun x hx => (hf x (hIcc hx)).continuousAt.continuousWithinAt)
      (fun x hx => (hf x (hIcc (Ico_subset_Icc_self hx))).hasDerivWithinAt)
      (fun x hx => hg x (hIcc (Ico_subset_Icc_self hx)))
    exact right_mem_Icc.mpr ha.2.le
  have hleft : Tendsto (fun a => ‖f t - f a‖) (𝓝[>] 0) (𝓝 ‖f t - 0‖) :=
    (tendsto_const_nhds.sub hf₀).norm
  have hid : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hright : Tendsto (fun a => bound * (t - a)) (𝓝[>] 0) (𝓝 (bound * (t - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hid)
  simpa only [sub_zero] using le_of_tendsto_of_tendsto hleft hright hslope

/-- A solution of `t f''(t) = f(t)` on the positive half-line with zero boundary data
for both `f` and its derivative vanishes on the positive half-line. -/
theorem eq_zero_of_singularSecondOrder {f g : ℝ → E}
    (hf : ∀ t > 0, HasDerivAt f (g t) t)
    (hg : ∀ t > 0, HasDerivAt g (t⁻¹ • f t) t)
    (hf₀ : Tendsto f (𝓝[>] 0) (𝓝 0))
    (hg₀ : Tendsto g (𝓝[>] 0) (𝓝 0))
    {t : ℝ} (ht : 0 < t) : f t = 0 := by
  have hnear : ∀ᶠ x in 𝓝[>] (0 : ℝ), ‖g x‖ < 1 :=
    hg₀.norm.eventually_lt_const (by simp)
  obtain ⟨d, hd, hdBound⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hnear
  let r := min d 1 / 2
  have hr : 0 < r := half_pos (lt_min hd zero_lt_one)
  have hrd : r < d := (half_lt_self (lt_min hd zero_lt_one)).trans_le (min_le_left _ _)
  have hr₁ : r < 1 := (half_lt_self (lt_min hd zero_lt_one)).trans_le (min_le_right _ _)
  -- Each pair of mean value estimates multiplies the bound on the derivative by `r`.
  have hgBound (n : ℕ) : ∀ x ∈ Ioc 0 r, ‖g x‖ ≤ r ^ n := by
    induction n with
    | zero =>
      intro x hx
      simpa using (hdBound ⟨hx.1, hx.2.trans_lt hrd⟩).le
    | succ n ih =>
      have hfBound {x : ℝ} (hx : x ∈ Ioc 0 r) : ‖f x‖ ≤ r ^ n * x :=
        norm_le_mul_of_hasDerivAt_of_tendsto_zero (fun y hy => hf y hy.1) ih hf₀ hx
      have hsecond (x : ℝ) (hx : x ∈ Ioc 0 r) : ‖x⁻¹ • f x‖ ≤ r ^ n := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx.1)]
        calc
          x⁻¹ * ‖f x‖ ≤ x⁻¹ * (r ^ n * x) :=
            mul_le_mul_of_nonneg_left (hfBound hx) (inv_nonneg.mpr hx.1.le)
          _ = r ^ n := by rw [mul_left_comm, inv_mul_cancel₀ hx.1.ne', mul_one]
      intro x hx
      calc
        ‖g x‖ ≤ r ^ n * x :=
          norm_le_mul_of_hasDerivAt_of_tendsto_zero (fun y hy => hg y hy.1) hsecond hg₀ hx
        _ ≤ r ^ (n + 1) := by
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_left hx.2 (pow_nonneg hr.le _)
  have hgZero {x : ℝ} (hx : x ∈ Ioc 0 r) : g x = 0 :=
    norm_le_zero_iff.mp <| le_of_tendsto_of_tendsto' tendsto_const_nhds
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr₁) (fun n => hgBound n x hx)
  have hfZero {x : ℝ} (hx : x ∈ Ioc 0 r) : f x = 0 := by
    have h := norm_le_mul_of_hasDerivAt_of_tendsto_zero
      (fun y hy => hf y hy.1) (fun y hy => (norm_le_zero_iff.mpr (hgZero hy))) hf₀ hx
    exact norm_le_zero_iff.mp (by simpa only [zero_mul] using h)
  by_cases ht₀ : t ≤ r
  · exact hfZero ⟨ht, ht₀⟩
  -- On an interval bounded away from zero the system has a bounded coefficient.
  have hpair := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun x => (f x, g x)) (f' := fun x => (g x, x⁻¹ • f x))
    (K := max 1 r⁻¹) (a := r) (b := t)
    (fun x hx => ((hf x (hr.trans_le hx.1)).prodMk
      (hg x (hr.trans_le hx.1))).continuousAt.continuousWithinAt)
    (fun x hx => ((hf x (hr.trans_le hx.1)).prodMk
      (hg x (hr.trans_le hx.1))).hasDerivWithinAt)
    (by simp [hfZero ⟨hr, le_rfl⟩, hgZero ⟨hr, le_rfl⟩])
    (by
      intro x hx
      have hx₀ : 0 < x := hr.trans_le hx.1
      rw [Prod.norm_def, Prod.norm_def, max_le_iff]
      constructor
      · calc
          ‖g x‖ ≤ max ‖f x‖ ‖g x‖ := le_max_right _ _
          _ ≤ max 1 r⁻¹ * max ‖f x‖ ‖g x‖ :=
            le_mul_of_one_le_left (le_trans (norm_nonneg _) (le_max_right _ _))
              (le_max_left _ _)
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx₀)]
        exact mul_le_mul
          ((inv_anti₀ hr hx.1).trans (le_max_right _ _)) (le_max_left _ _)
          (norm_nonneg _) (zero_le_one.trans (le_max_left _ _)))
    t (right_mem_Icc.mpr (le_of_not_ge ht₀))
  exact congrArg Prod.fst hpair

end Omega
