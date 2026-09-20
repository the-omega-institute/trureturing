/- GID: D5/S3/FluidDynamics/Volterra/SingularKernelUniqueness
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Volterra/SingularKernelUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singular Volterra comparison forces pointwise zero on every compact time interval. -/

import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter MeasureTheory Topology

namespace D5.S3.FluidDynamics.Volterra.SingularKernelUniqueness

/-- Uniqueness for the scalar singular Volterra comparison on an arbitrary compact interval. -/
theorem eq_zero_of_le_sqrt_kernel_integral
    (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C) (d : ℝ → ℝ)
    (hd : ContinuousOn d (Icc 0 T))
    (hd_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ d t)
    (hd_le : ∀ t ∈ Icc 0 T,
      d t ≤ C * ∫ s in (0)..t, (Real.sqrt (t - s))⁻¹ * d s) :
    ∀ t ∈ Icc 0 T, d t = 0 := by
  let k : ℝ → ℝ := fun r => (Real.sqrt r)⁻¹
  have hk_nonneg (r : ℝ) : 0 ≤ k r := inv_nonneg.mpr (Real.sqrt_nonneg r)
  have hk_int (t : ℝ) (ht : 0 ≤ t) : IntervalIntegrable k volume 0 t := by
    apply IntervalIntegrable.congr (f := fun r : ℝ => r ^ (-(1 / 2 : ℝ)))
      (fun r hr => ?_) (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
    have hr0 : 0 ≤ r := (show r ∈ Ioc 0 t by simpa [uIoc_of_le ht] using hr).1.le
    dsimp [k]
    rw [Real.rpow_neg hr0, Real.sqrt_eq_rpow]
  have hd_int (t : ℝ) (ht : t ∈ Icc 0 T) :
      IntervalIntegrable (fun s => k (t - s) * d s) volume 0 t := by
    have hki : IntervalIntegrable (fun s => k (t - s)) volume 0 t := by
      simpa using ((hk_int t ht.1).comp_sub_left t).symm
    apply hki.mul_continuousOn
    rw [uIcc_of_le ht.1]
    exact hd.mono (Icc_subset_Icc le_rfl ht.2)
  let F : ℕ → ℝ → ℝ := fun n r => k r * Real.exp (-(n : ℝ) * r)
  have hF_int (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : IntervalIntegrable (F n) volume 0 t :=
    (hk_int t ht).mul_continuousOn
      ((continuous_const.mul continuous_id).rexp.continuousOn)
  let J : ℕ → ℝ := fun n => ∫ r in (0)..T, F n r
  have hJ : Tendsto J atTop (𝓝 0) := by
    have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (a := 0) (b := T) (μ := volume) (F := F) (f := fun _ => (0 : ℝ)) k
      (Eventually.of_forall fun n => (hF_int n T hT).aestronglyMeasurable_restrict_uIoc)
      (Eventually.of_forall fun n => Eventually.of_forall fun r hr => by
        have hr0 : 0 ≤ r := (show r ∈ Ioc 0 T by simpa [uIoc_of_le hT] using hr).1.le
        have hexp : Real.exp (-(n : ℝ) * r) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) hr0
        dsimp [F]
        rw [abs_of_nonneg (mul_nonneg (hk_nonneg r) (Real.exp_pos _).le)]
        simpa using mul_le_mul_of_nonneg_left hexp (hk_nonneg r))
      (hk_int T hT)
      (Eventually.of_forall fun r hr => by
        have hr0 : 0 < r := (show r ∈ Ioc 0 T by simpa [uIoc_of_le hT] using hr).1
        have he : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * r)) atTop (𝓝 0) := by
          simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
            (Tendsto.atTop_mul_const hr0 tendsto_natCast_atTop_atTop)
        simpa [F] using he.const_mul (k r))
    simpa [J] using hlim
  have hCJ : Tendsto (fun n => C * J n) atTop (𝓝 0) := by
    simpa using hJ.const_mul C
  obtain ⟨n, hn⟩ := (hCJ.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).exists
  let w : ℝ → ℝ := fun t => Real.exp (-(n : ℝ) * t)
  have hw_pos (t : ℝ) : 0 < w t := Real.exp_pos _
  have hw_cont : Continuous w := (continuous_const.mul continuous_id).rexp
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hT) (hw_cont.continuousOn.mul hd)
  let M := w t₀ * d t₀
  have hM_nonneg : 0 ≤ M := mul_nonneg (hw_pos t₀).le (hd_nonneg t₀ ht₀)
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) : w t * d t ≤ C * J n * M := by
    have hpoint (s : ℝ) (hs : s ∈ Icc 0 t) :
        w t * (k (t - s) * d s) ≤ M * (k (t - s) * w (t - s)) := by
      have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
      have hws : w (t - s) * w s = w t := by
        dsimp [w]
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        w t * (k (t - s) * d s) =
            (k (t - s) * w (t - s)) * (w s * d s) := by
          rw [mul_assoc, ← mul_assoc (w (t - s)), hws]
          ring
        _ ≤ (k (t - s) * w (t - s)) * M :=
          mul_le_mul_of_nonneg_left (hmax hsT)
            (mul_nonneg (hk_nonneg _) (hw_pos _).le)
        _ = M * (k (t - s) * w (t - s)) := mul_comm _ _
    have hF_reflect : IntervalIntegrable (fun s => k (t - s) * w (t - s)) volume 0 t := by
      simpa [F, w] using ((hF_int n t ht.1).comp_sub_left t).symm
    have hint := intervalIntegral.integral_mono_on ht.1
      ((hd_int t ht).const_mul (w t)) (hF_reflect.const_mul M) hpoint
    have hsub : (∫ s in (0)..t, k (t - s) * w (t - s)) = ∫ r in (0)..t, F n r := by
      simpa [F, w] using intervalIntegral.integral_comp_sub_left
        (a := 0) (b := t) (fun r => F n r) t
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hsub] at hint
    have hmass : (∫ r in (0)..t, F n r) ≤ J n := by
      apply intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Eventually.of_forall fun r => ?_) (hF_int n T hT)
      exact mul_nonneg (hk_nonneg r) (Real.exp_pos _).le
    calc
      w t * d t ≤ w t * (C * ∫ s in (0)..t, k (t - s) * d s) :=
        mul_le_mul_of_nonneg_left (hd_le t ht) (hw_pos t).le
      _ = C * (w t * ∫ s in (0)..t, k (t - s) * d s) := by ring
      _ ≤ C * (M * ∫ r in (0)..t, F n r) := mul_le_mul_of_nonneg_left hint hC
      _ ≤ C * (M * J n) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmass hM_nonneg) hC
      _ = C * J n * M := by ring
  have hM_le : M ≤ C * J n * M := hbound t₀ ht₀
  have hM_zero : M = 0 := by nlinarith
  intro t ht
  have hwd : w t * d t ≤ 0 := by simpa [← hM_zero] using hmax ht
  exact le_antisymm (by nlinarith [hw_pos t]) (hd_nonneg t ht)

end D5.S3.FluidDynamics.Volterra.SingularKernelUniqueness
