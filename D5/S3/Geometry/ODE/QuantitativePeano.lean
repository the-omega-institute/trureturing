/- GID: D5/S3/Geometry/ODE/QuantitativePeano
   generality: G
   mirror-B: D5/B/S3/Geometry/ODE/QuantitativePeano
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli]
   utility: none
   digest: Delayed Tonelli approximations yield a quantitative cylinder integral solution. -/

/-
Copyright (c) 2026 Julian Rolfes. All rights reserved.
Released under Apache 2.0 license, reproduced at the end of this file.
Authors: Julian Rolfes, Luke Schleef, Philipp Svinger, Paul Niessner, Florian Grube

Adapted from philipp-svinger/mathlib4@a6c8f2f1ae84638491c3f1635c9f8448bda1e727,
Mathlib/Analysis/ODE/Peano.lean, for the native pinned Mathlib.
The integral construction retains its quantitative cylinder hypotheses.
Auxiliary proof steps are local to the integral theorem.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
open Metric Set Filter
open scoped NNReal BoundedContinuousFunction
namespace D5.S3.Geometry.ODE.QuantitativePeano

structure IsPeanoODE {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E → E) (tmin tmax t₀ : ℝ) (x₀ : E) (r L : ℝ≥0) : Prop where
  /-- The initial time belongs to the time interval. -/
  t₀_mem : t₀ ∈ Icc tmin tmax
  /-- The vector field is jointly continuous in time and space on the cylinder. -/
  continuousOn : ContinuousOn f.uncurry (Icc tmin tmax ×ˢ closedBall x₀ r)
  /-- `L` is an upper bound of the norm of the vector field. -/
  norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ r, ‖f t x‖ ≤ L
  /-- The time interval of validity. -/
  mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ r

namespace IsPeanoODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def stepSize (t₀ tmax : ℝ) (n : ℕ) : ℝ := (tmax - t₀) / n

noncomputable def delayedInput (t₀ tmax : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  max (t - stepSize t₀ tmax n) t₀

noncomputable def tonelliIterate (f : ℝ → E → E) (t₀ tmax : ℝ) (x₀ : E) (n : ℕ) :
    ℕ → ℝ → E
  | 0 => fun _ ↦ x₀
  | k + 1 =>
      fun t ↦ x₀ + ∫ s in t₀..t,
        f s (tonelliIterate f t₀ tmax x₀ n k (delayedInput t₀ tmax n s))

noncomputable def tonelliApproximation
    (f : ℝ → E → E) (t₀ tmax : ℝ) (x₀ : E) (n : ℕ) : ℝ → E :=
  fun t ↦ tonelliIterate f t₀ tmax x₀ (n + 1) (n + 1) t

variable [FiniteDimensional ℝ E]

variable {f : ℝ → E → E} {tmin tmax t₀ : ℝ} {x₀ : E} {r L : ℝ≥0}

/-- A continuous bounded finite-dimensional cylinder field admits an integral solution
on the specified closed interval, with no spatial Lipschitz hypothesis. -/
theorem exists_eq_forall_mem_Icc_eq_integral
    (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) :
    ∃ α : ℝ → E, ContinuousOn α (Icc tmin tmax) ∧ MapsTo α (Icc tmin tmax) (closedBall x₀ r) ∧
      ∀ t ∈ Icc tmin tmax, α t = x₀ + ∫ s in t₀..t, f s (α s) := by
  classical
  have Icc_t0_subset_Icc {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax) :
      Icc t₀ tmax ⊆ Icc tmin tmax :=
    Icc_subset_Icc_left ht₀.1
  have mul_abs_sub_le_radius {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {r : ℝ≥0} {L : ℝ≥0} {t : ℝ}
      (h_mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ r)
      (ht : t ∈ Icc t₀ tmax) : L * |t - t₀| ≤ r := by
    have h_diff : t - t₀ ≤ max (tmax - t₀) (t₀ - tmin) := by
      calc
        t - t₀ ≤ tmax - t₀ := sub_le_sub_right ht.2 t₀
        tmax - t₀ ≤ max (tmax - t₀) (t₀ - tmin) := le_max_left (tmax - t₀) (t₀ - tmin)
    calc
      L * |t - t₀| = L * (t - t₀) := by rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
      L * (t - t₀) ≤ L * max (tmax - t₀) (t₀ - tmin) := by gcongr
      L * max (tmax - t₀) (t₀ - tmin) ≤ r := h_mul_max_le
  have stepSize_nonneg {t₀ tmax : ℝ} (n : ℕ) (ht₀ : t₀ ≤ tmax) :
      0 ≤ stepSize t₀ tmax n :=
    div_nonneg (sub_nonneg.mpr ht₀) (Nat.cast_nonneg n)
  have mapsTo_delayedInput_previous_interval
      {t₀ tmax : ℝ} (n k : ℕ) (ht₀ : t₀ ≤ tmax) :
      MapsTo (delayedInput t₀ tmax n)
        (Icc t₀ (t₀ + (k + 1 : ℝ) * stepSize t₀ tmax n))
        (Icc t₀ (t₀ + (k : ℝ) * stepSize t₀ tmax n)) := by
    intro s hs
    rw [mem_Icc] at hs ⊢
    have h_mul_nonneg : 0 ≤ (k : ℝ) * stepSize t₀ tmax n :=
      mul_nonneg (Nat.cast_nonneg k) (stepSize_nonneg n ht₀)
    exact ⟨le_max_right _ _, max_le (by linarith) (by linarith)⟩
  have mapsTo_delayedInput {t₀ tmax : ℝ} (n : ℕ) (ht₀ : t₀ ≤ tmax) :
      MapsTo (delayedInput t₀ tmax n) (Icc t₀ tmax) (Icc t₀ tmax) := by
    intro s hs
    rw [mem_Icc] at hs ⊢
    have := stepSize_nonneg n ht₀
    exact ⟨le_max_right _ _, max_le (by linarith) ht₀⟩
  have lipschitzWith_delayedInput {t₀ tmax : ℝ} (n : ℕ) :
      LipschitzWith 1 (delayedInput t₀ tmax n) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa [delayedInput, Real.dist_eq, sub_sub_sub_cancel_right] using
      abs_max_sub_max_le_abs (x - stepSize t₀ tmax n) (y - stepSize t₀ tmax n) t₀
  have tonelliIterate_zero (f : ℝ → E → E) (t₀ tmax : ℝ) (x₀ : E) (n : ℕ) :
      tonelliIterate f t₀ tmax x₀ n 0 = fun _ ↦ x₀ := rfl
  have tonelliIterate_succ (f : ℝ → E → E) (t₀ tmax : ℝ) (x₀ : E) (n k : ℕ) :
      tonelliIterate f t₀ tmax x₀ n (k + 1) =
        fun t ↦ x₀ + ∫ s in t₀..t,
          f s (tonelliIterate f t₀ tmax x₀ n k (delayedInput t₀ tmax n s)) := rfl
  have tonelliIterate_apply_t₀
      (f : ℝ → E → E) {t₀ tmax : ℝ} (x₀ : E) (n : ℕ) (k : ℕ) :
      tonelliIterate f t₀ tmax x₀ n k t₀ = x₀ := by
    cases k <;> simp [tonelliIterate_succ, tonelliIterate_zero]
  have tonelliIterate_bounds
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) (n k : ℕ) :
      MapsTo (tonelliIterate f t₀ tmax x₀ n k) (Icc t₀ tmax) (closedBall x₀ r) ∧
      LipschitzOnWith L (tonelliIterate f t₀ tmax x₀ n k) (Icc t₀ tmax) := by
    induction k with
    | zero =>
      exact
        ⟨fun _ _ ↦ by simp [mem_closedBall, tonelliIterate],
          (LipschitzWith.const x₀).weaken L.2 |>.lipschitzOnWith⟩
    | succ k hk =>
      have h_delayed : MapsTo (delayedInput t₀ tmax n) (Icc t₀ tmax) (Icc t₀ tmax) :=
        mapsTo_delayedInput n hf.t₀_mem.2
      have h_iterate_cont := hk.2.continuousOn
      have h_map : MapsTo
          (fun s ↦ tonelliIterate f t₀ tmax x₀ n k (delayedInput t₀ tmax n s))
          (Icc t₀ tmax) (closedBall x₀ r) :=
        hk.1.comp h_delayed
      have h_cont :
          ContinuousOn
            (fun s ↦ f s (tonelliIterate f t₀ tmax x₀ n k (delayedInput t₀ tmax n s)))
            (uIcc t₀ tmax) := by
        rw [uIcc_of_le hf.t₀_mem.2]
        exact hf.continuousOn.comp
          (f := fun s ↦ (s, tonelliIterate f t₀ tmax x₀ n k (delayedInput t₀ tmax n s)))
          (by fun_prop [delayedInput])
          (fun t ht ↦ ⟨Icc_t0_subset_Icc hf.t₀_mem ht, h_map ht⟩)
      have h_int :
          IntervalIntegrable
            (fun s ↦ f s (tonelliIterate f t₀ tmax x₀ n k (delayedInput t₀ tmax n s)))
            MeasureTheory.volume t₀ tmax :=
        ContinuousOn.intervalIntegrable h_cont
      have h_lip : LipschitzOnWith L (tonelliIterate f t₀ tmax x₀ n (k + 1)) (Icc t₀ tmax) := by
        rw [lipschitzOnWith_iff_dist_le_mul]
        intro a ha b hb
        rw [Real.dist_eq, dist_eq_norm, tonelliIterate_succ, add_sub_add_left_eq_sub,
          intervalIntegral.integral_interval_sub_left]
        · refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
          have ht' := uIoc_subset_uIcc.trans (uIcc_subset_Icc hb ha) ht
          exact hf.norm_le t (Icc_t0_subset_Icc hf.t₀_mem ht') _ (h_map ht')
        · exact h_int.mono_set (uIcc_subset_uIcc left_mem_uIcc <| Icc_subset_uIcc ha)
        · exact h_int.mono_set (uIcc_subset_uIcc left_mem_uIcc <| Icc_subset_uIcc hb)
      refine ⟨fun t ht ↦ ?_, h_lip⟩
      rw [mem_closedBall]
      nth_rewrite 2 [← tonelliIterate_apply_t₀ f x₀ n (k + 1)]
      refine (h_lip.dist_le_mul t ht t₀ <| left_mem_Icc.mpr hf.t₀_mem.2).trans ?_
      rw [Real.dist_eq]
      exact mul_abs_sub_le_radius hf.mul_max_le ht
  have mapsTo_tonelliIterate_closedBall
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) (n : ℕ) (k : ℕ) :
      MapsTo (tonelliIterate f t₀ tmax x₀ n k) (Icc t₀ tmax) (closedBall x₀ r) :=
    tonelliIterate_bounds hf n k |>.1
  have lipschitzOnWith_tonelliIterate
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) (n : ℕ) (k : ℕ) :
      LipschitzOnWith L (tonelliIterate f t₀ tmax x₀ n k) (Icc t₀ tmax) :=
    tonelliIterate_bounds hf n k |>.2
  have tonelliIterate_eq_succ_on_Icc
      {f : ℝ → E → E} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} (n : ℕ) (k : ℕ) (ht₀ : t₀ ≤ tmax) (t : ℝ)
      (ht : t ∈ Icc t₀ (t₀ + k * stepSize t₀ tmax n)) :
      tonelliIterate f t₀ tmax x₀ n k t = tonelliIterate f t₀ tmax x₀ n (k + 1) t := by
    induction k generalizing t with
    | zero =>
      obtain rfl : t = t₀ := by simp_all
      simp only [tonelliIterate_zero]
      simp [tonelliIterate_succ]
    | succ k ih =>
      push_cast at ht
      rw [tonelliIterate_succ, tonelliIterate_succ, add_right_inj]
      apply intervalIntegral.integral_congr
      intro s hs
      simp only [ih _ (mapsTo_delayedInput_previous_interval n k ht₀
        (uIcc_subset_Icc (left_mem_Icc.mpr (ht.1.trans ht.2)) ht hs))]
  have mapsTo_tonelliApproximation_closedBall
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) (n : ℕ) :
      MapsTo (tonelliApproximation f t₀ tmax x₀ n) (Icc t₀ tmax) (closedBall x₀ r) :=
    mapsTo_tonelliIterate_closedBall hf (n + 1) (n + 1)
  have lipschitzOnWith_tonelliApproximation
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) (n : ℕ) :
      LipschitzOnWith L (tonelliApproximation f t₀ tmax x₀ n) (Icc t₀ tmax) :=
    lipschitzOnWith_tonelliIterate hf (n + 1) (n + 1)
  have tonelliApproximation_apply_t₀
      (f : ℝ → E → E) {t₀ tmax : ℝ} (x₀ : E) (n : ℕ) :
      tonelliApproximation f t₀ tmax x₀ n t₀ = x₀ :=
    tonelliIterate_apply_t₀ f x₀ (n + 1) (n + 1)
  have tonelliApproximation_eq_integral
      {f : ℝ → E → E} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} (n : ℕ) (t : ℝ) (ht : t ∈ Icc t₀ tmax) :
      tonelliApproximation f t₀ tmax x₀ n t =
        x₀ + ∫ s in t₀..t,
          f s (tonelliApproximation f t₀ tmax x₀ n (delayedInput t₀ tmax (n + 1) s)) := by
    have h_succ : ∀ t ∈ Icc t₀ tmax, tonelliApproximation f t₀ tmax x₀ n t =
        tonelliIterate f t₀ tmax x₀ (n + 1) (n + 2) t := by
      intro t ht
      apply tonelliIterate_eq_succ_on_Icc (n + 1) (n + 1) (ht.1.trans ht.2)
      have h_end : t₀ + ((n : ℝ) + 1) * stepSize t₀ tmax (n + 1) = tmax := by
        rw [stepSize]
        grind
      simpa only [Nat.cast_add, Nat.cast_one, h_end] using ht
    rw [h_succ t ht, tonelliIterate_succ]
    rfl
  let boundedTonelliApproximation
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) (n : ℕ) : Icc t₀ tmax →ᵇ E :=
    .mkOfCompact ⟨(Icc t₀ tmax).domRestrict (tonelliApproximation f t₀ tmax x₀ n),
      continuousOn_iff_continuous_domRestrict.mp
        (lipschitzOnWith_tonelliApproximation hf n).continuousOn⟩
  have lipschitzWith_boundedTonelliApproximation
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) (n : ℕ) :
      LipschitzWith L (boundedTonelliApproximation hf n) :=
    lipschitzWith_iff_dist_le_mul.mpr fun t s ↦
      (lipschitzOnWith_tonelliApproximation hf n).dist_le_mul t.val t.2 s.val s.2
  have equicontinuous_boundedTonelliApproximation
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) :
      Equicontinuous (fun n ↦ (boundedTonelliApproximation hf n).toFun) :=
    (LipschitzWith.uniformEquicontinuous _ L
      (lipschitzWith_boundedTonelliApproximation hf)).equicontinuous
  have isCompact_closure_range_boundedTonelliApproximation
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) :
      IsCompact (closure (range (boundedTonelliApproximation hf))) := by
    apply BoundedContinuousFunction.arzela_ascoli (closedBall x₀ r) (isCompact_closedBall _ _)
    · rintro g x ⟨n, rfl⟩
      exact mapsTo_tonelliApproximation_closedBall hf n x.2
    · exact fun x U hU ↦ (equicontinuous_boundedTonelliApproximation hf x U hU).mono (by simp)
  have exists_tendsto_subseq_boundedTonelliApproximation
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) :
      ∃ β : Icc t₀ tmax →ᵇ E, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (boundedTonelliApproximation hf ∘ φ) atTop (nhds β) := by
    obtain ⟨β, _, φ, hφ_mono, hφ_tendsto⟩ :=
      (isCompact_closure_range_boundedTonelliApproximation hf).tendsto_subseq
        fun n ↦ subset_closure ⟨n, rfl⟩
    exact ⟨β, φ, hφ_mono, hφ_tendsto⟩
  have exists_tendstoUniformlyOn_subseq_tonelliApproximation
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) :
      ∃ α : ℝ → E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ContinuousOn α (Icc t₀ tmax) ∧
        MapsTo α (Icc t₀ tmax) (closedBall x₀ r) ∧
          TendstoUniformlyOn (tonelliApproximation f t₀ tmax x₀ ∘ φ) α atTop (Icc t₀ tmax) := by
    obtain ⟨β, φ, hφ_mono, hβ_tendsto⟩ := exists_tendsto_subseq_boundedTonelliApproximation hf
    let α : ℝ → E := fun t ↦ if h : t ∈ Icc t₀ tmax then β ⟨t, h⟩ else 0
    have hα : ∀ t : Icc t₀ tmax, α t = β t := fun t ↦ dif_pos t.2
    have h_uniform : TendstoUniformly (fun n ↦ boundedTonelliApproximation hf (φ n)) β atTop :=
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hβ_tendsto
    refine ⟨α, φ, hφ_mono, ?_, ?_, ?_⟩
    · rw [continuousOn_iff_continuous_domRestrict,
        show (Icc t₀ tmax).domRestrict α = β from funext hα]
      exact β.continuous
    · intro t ht
      rw [hα ⟨t, ht⟩]
      refine isClosed_closedBall.mem_of_tendsto (h_uniform.tendsto_at ⟨t, ht⟩) ?_
      filter_upwards with n using mapsTo_tonelliApproximation_closedBall hf (φ n) ht
    · rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe,
        show α ∘ Subtype.val = ⇑β from funext hα]
      exact h_uniform
  have tendsto_stepSize_zero {tmax : ℝ} {t₀ : ℝ} : Tendsto (stepSize t₀ tmax) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (tmax - t₀)
  have tendsto_delayedInput_id {tmax : ℝ} {t₀ : ℝ} (t : ℝ) (ht : t₀ ≤ t) :
      Tendsto (fun n ↦ delayedInput t₀ tmax n t) atTop (nhds t) := by
    have h_tendsto : Tendsto (fun n ↦ max (t - stepSize t₀ tmax n) t₀) atTop
        (nhds (max (t - 0) t₀)) :=
      Tendsto.max (Tendsto.sub tendsto_const_nhds tendsto_stepSize_zero) tendsto_const_nhds
    simp only [sub_zero, max_eq_left ht] at h_tendsto
    exact h_tendsto
  have tendsto_tonelliApproximation_delayedInput_of_tendstoUniformlyOn_tonelliApproximation
      {f : ℝ → E → E} {α : ℝ → E} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {φ : ℕ → ℕ}
      (hφ : StrictMono φ)
      (hα : ContinuousOn α (Icc t₀ tmax))
      (h_tendsto : TendstoUniformlyOn (tonelliApproximation f t₀ tmax x₀ ∘ φ) α atTop
        (Icc t₀ tmax))
      (t : ℝ) (ht : t ∈ Icc t₀ tmax) :
      Tendsto
        (fun n ↦
          tonelliApproximation f t₀ tmax x₀ (φ n) (delayedInput t₀ tmax (φ n + 1) t))
        atTop (nhds (α t)) := by
    refine h_tendsto.tendsto_comp (hα t ht) (tendsto_nhdsWithin_iff.mpr ?_)
    exact
      ⟨(tendsto_delayedInput_id t ht.1).comp <| (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop,
        Eventually.of_forall (fun _ ↦ mapsTo_delayedInput _ (ht.1.trans ht.2) ht)⟩
  have continuousOn_tonelliApproximation_delayedInput
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) (n : ℕ) :
      ContinuousOn
        (fun t ↦ tonelliApproximation f t₀ tmax x₀ n (delayedInput t₀ tmax (n + 1) t))
        (Icc t₀ tmax) :=
    (lipschitzOnWith_tonelliApproximation hf n).continuousOn.comp
      (lipschitzWith_delayedInput _).continuous.continuousOn
        (mapsTo_delayedInput _ hf.t₀_mem.2)
  have mapsTo_tonelliApproximation_delayedInput
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) (n : ℕ) :
      MapsTo
        (fun t ↦ tonelliApproximation f t₀ tmax x₀ n (delayedInput t₀ tmax (n + 1) t))
        (Icc t₀ tmax) (closedBall x₀ r) :=
    (mapsTo_tonelliApproximation_closedBall hf n).comp
      (mapsTo_delayedInput _ hf.t₀_mem.2)
  have continuousOn_comp_tonelliApproximation_delayedInput
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) (n : ℕ) :
      ContinuousOn
        (fun t ↦ f t (tonelliApproximation f t₀ tmax x₀ n (delayedInput t₀ tmax (n + 1) t)))
        (Icc t₀ tmax) := by
    apply hf.continuousOn.comp
      (ContinuousOn.prodMk continuousOn_id (continuousOn_tonelliApproximation_delayedInput hf n))
    intro s hs
    exact ⟨mem_Icc.mp (Icc_t0_subset_Icc hf.t₀_mem hs),
      mapsTo_tonelliApproximation_delayedInput hf n hs⟩
  have mem_Icc_of_mem_uIoc {tmax : ℝ} {t₀ : ℝ} {s t : ℝ} (ht : t ∈ Icc t₀ tmax)
      (hs : s ∈ uIoc t₀ t) : s ∈ Icc t₀ tmax :=
    Icc_subset_Icc_right ht.2 (Ioc_subset_Icc_self (uIoc_of_le ht.1 ▸ hs))
  have forall_mem_Icc_eq_integral_of_eqOn
      {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ} {x₀ : E} {a b : ℝ} {β : ℝ → E} (ht₀ : t₀ ∈ Icc a b)
      (hαβ : EqOn α β (Icc a b)) (hβ : ∀ t ∈ Icc a b, β t = x₀ + ∫ u in t₀..t, f u (β u)) :
      ∀ t ∈ Icc a b, α t = x₀ + ∫ u in t₀..t, f u (α u) := fun t ht ↦ by
    have h : EqOn (fun u ↦ f u (β u)) (fun u ↦ f u (α u)) (uIcc t₀ t) :=
      fun u hu ↦ by simp only [hαβ (uIcc_subset_Icc ht₀ ht hu)]
    rw [hαβ ht, hβ t ht, intervalIntegral.integral_congr h]
  have exists_eq_forall_mem_Icc_eq_integral_forward
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) :
      ∃ α : ℝ → E, ContinuousOn α (Icc t₀ tmax) ∧ MapsTo α (Icc t₀ tmax) (closedBall x₀ r) ∧
        ∀ t ∈ Icc t₀ tmax, α t = x₀ + ∫ s in t₀..t, f s (α s) := by
    obtain ⟨α, φ, hφ_mono, hα_cont, hα_maps, hα_tendsto⟩ :=
      exists_tendstoUniformlyOn_subseq_tonelliApproximation hf
    refine ⟨α, hα_cont, hα_maps, fun t ht ↦ tendsto_nhds_unique
      (hα_tendsto.tendsto_at ht)
      ((Tendsto.const_add x₀ ?_).congr
        (fun n ↦ (tonelliApproximation_eq_integral (φ n) t ht).symm))⟩
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (bound := fun _ ↦ L)
      _ _ intervalIntegrable_const _
    · filter_upwards with n
      have h_cont := continuousOn_comp_tonelliApproximation_delayedInput hf (φ n)
      rw [uIoc_of_le ht.1]
      exact (h_cont.mono (Ioc_subset_Icc_self.trans
        (Icc_subset_Icc le_rfl ht.2))).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards with n
      filter_upwards with s hs
      have hs := mem_Icc_of_mem_uIoc ht hs
      apply hf.norm_le s (Icc_t0_subset_Icc hf.t₀_mem hs)
      exact mapsTo_tonelliApproximation_delayedInput hf (φ n) hs
    · have h_lim :=
        tendsto_tonelliApproximation_delayedInput_of_tendstoUniformlyOn_tonelliApproximation
          hφ_mono hα_cont hα_tendsto
      filter_upwards with s hs
      have hs := mem_Icc_of_mem_uIoc ht hs
      apply Tendsto.comp
        (f := fun n ↦
          (s, tonelliApproximation f t₀ tmax x₀ (φ n) (delayedInput t₀ tmax (φ n + 1) s)))
        (hf.continuousOn.continuousWithinAt (x := (s, α s)) _)
      · refine tendsto_nhdsWithin_iff.mpr
          ⟨Tendsto.prodMk_nhds tendsto_const_nhds (h_lim s hs), ?_⟩
        apply Eventually.of_forall
        exact fun n ↦ mem_prod.mpr
          ⟨Icc_t0_subset_Icc hf.t₀_mem hs,
            MapsTo.comp (mapsTo_tonelliApproximation_closedBall hf _)
              (mapsTo_delayedInput _ hf.t₀_mem.2) hs⟩
      · refine ⟨Icc_t0_subset_Icc hf.t₀_mem hs, ?_⟩
        apply IsClosed.mem_of_tendsto isClosed_closedBall (hα_tendsto.tendsto_at hs)
        exact Eventually.of_forall (fun n ↦ mapsTo_tonelliApproximation_closedBall hf (φ n) hs)
  have exists_eq_forall_mem_Icc_eq_integral_backward
      {f : ℝ → E → E} {tmin : ℝ} {tmax : ℝ} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {L : ℝ≥0}
      (hf : IsPeanoODE f tmin tmax t₀ x₀ r L) :
      ∃ α : ℝ → E, ContinuousOn α (Icc tmin t₀) ∧ MapsTo α (Icc tmin t₀) (closedBall x₀ r) ∧
        ∀ t ∈ Icc tmin t₀,
          α t = x₀ + ∫ s in t₀..t, f s (α s) := by
    let g : ℝ → E → E := fun t x ↦ -f (-t) x
    let t₀' : ℝ := -t₀
    have h_g : IsPeanoODE g (-tmax) (-tmin) t₀' x₀ r L := by
      constructor
      · exact ⟨neg_le_neg hf.t₀_mem.2, neg_le_neg hf.t₀_mem.1⟩
      · refine ContinuousOn.neg (hf.continuousOn.comp
          (f := fun p : ℝ × E ↦ (-p.1, p.2)) ?_ ?_)
        · exact ContinuousOn.prodMap continuousOn_neg continuousOn_id
        · exact fun p hp ↦ ⟨⟨le_neg_of_le_neg hp.1.2, neg_le_of_neg_le hp.1.1⟩, hp.2⟩
      · intro t ht x hx
        simpa [g] using hf.norm_le (-t) ⟨le_neg_of_le_neg ht.2, neg_le_of_neg_le ht.1⟩ x hx
      · simpa [t₀', neg_add_eq_sub, sub_neg_eq_add, max_comm] using hf.mul_max_le
    obtain ⟨β, hβ_cont, hβ_maps, hβ_eq⟩ :=
      exists_eq_forall_mem_Icc_eq_integral_forward h_g
    let α := fun x ↦ β (-x)
    refine
      ⟨α, hβ_cont.comp continuousOn_neg (fun _ hs ↦ ⟨neg_le_neg hs.2, neg_le_neg hs.1⟩),
        fun t ht ↦ hβ_maps ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩, fun t ht ↦ ?_⟩
    have hβ_eq' := hβ_eq (-t) ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩
    rw [← intervalIntegral.integral_comp_neg] at hβ_eq'
    simpa [g, ← intervalIntegral.integral_symm] using hβ_eq'
  obtain ⟨α₁, hα₁_cont, hα₁_maps, hα₁_eq⟩ :=
    exists_eq_forall_mem_Icc_eq_integral_forward hf
  obtain ⟨α₂, hα₂_cont, hα₂_maps, hα₂_eq⟩ :=
    exists_eq_forall_mem_Icc_eq_integral_backward hf
  have ht₀₁ : t₀ ∈ Icc t₀ tmax := left_mem_Icc.mpr hf.t₀_mem.2
  have ht₀₂ : t₀ ∈ Icc tmin t₀ := right_mem_Icc.mpr hf.t₀_mem.1
  have hα₁_t₀ : α₁ t₀ = x₀ := by
    simpa using hα₁_eq t₀ ht₀₁
  have hα₂_t₀ : α₂ t₀ = x₀ := by
    simpa using hα₂_eq t₀ ht₀₂
  let α : ℝ → E := fun t ↦ if t₀ ≤ t then α₁ t else α₂ t
  have hα_eq_α₁ : EqOn α α₁ (Icc t₀ tmax) := fun t ht ↦ if_pos ht.1
  have hα_eq_α₂ : EqOn α α₂ (Icc tmin t₀) := fun t ht ↦ by
    rcases ht.2.lt_or_eq with h | h
    · exact if_neg (not_le.mpr h)
    · subst h
      exact (if_pos le_rfl).trans (hα₁_t₀.trans hα₂_t₀.symm)
  have h_union : Icc tmin t₀ ∪ Icc t₀ tmax = Icc tmin tmax :=
    Icc_union_Icc_eq_Icc hf.t₀_mem.1 hf.t₀_mem.2
  refine ⟨α, ?_, ?_, fun t ht ↦ ?_⟩
  · rw [← h_union]
    exact (hα₂_cont.congr hα_eq_α₂).union_of_isClosed (hα₁_cont.congr hα_eq_α₁)
      isClosed_Icc isClosed_Icc
  · rw [← h_union]
    exact (hα₂_maps.congr hα_eq_α₂.symm).union (hα₁_maps.congr hα_eq_α₁.symm)
  · rcases le_total t₀ t with h | h
    · exact forall_mem_Icc_eq_integral_of_eqOn ht₀₁ hα_eq_α₁ hα₁_eq t ⟨h, ht.2⟩
    · exact forall_mem_Icc_eq_integral_of_eqOn ht₀₂ hα_eq_α₂ hα₂_eq t ⟨ht.1, h⟩
end IsPeanoODE
end D5.S3.Geometry.ODE.QuantitativePeano

/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
