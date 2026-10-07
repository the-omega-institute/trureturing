/- GID: D5/S3/Arith/Lattices/Klartag/Walk/StepSecondMoment
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/StepSecondMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Gaussian.GaussianFourth
import D5.S3.Arith.Lattices.Klartag.Walk.StepTruncVariance

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Lemma43R
open D5.S3.Arith.Lattices.Klartag.Lemma43R2
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Walk.StepSecondMoment

open MeasureTheory
open ProbabilityTheory
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments

variable {n : ℕ}

/-- `∫ ‖ω k‖² = dim`, from `StepInputs.integral_norm_sq_starProjection` at the whole space. -/
theorem integral_norm_coord_sq (k : ℕ) :
    ∫ ω, ‖ChainSetup.coord (F := EuclideanSpace ℝ (UT n)) k ω‖ ^ 2
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      = (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) := by
  classical
  have hmap := ChainSetup.map_coord (F := EuclideanSpace ℝ (UT n)) k
  have hbase := StepInputs.integral_norm_sq_starProjection
    (E := EuclideanSpace ℝ (UT n)) (⊤ : Submodule ℝ (EuclideanSpace ℝ (UT n)))
  have htop : ∀ x : EuclideanSpace ℝ (UT n),
      (⊤ : Submodule ℝ (EuclideanSpace ℝ (UT n))).starProjection x = x := fun x =>
    Submodule.starProjection_eq_self_iff.2 Submodule.mem_top
  have hrank : (finrank ℝ (⊤ : Submodule ℝ (EuclideanSpace ℝ (UT n))) : ℝ)
      = (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) := by
    rw [finrank_top]
  have hbase' : ∫ x, ‖x‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (UT n)))
      = (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) := by
    rw [← hrank, ← hbase]
    exact integral_congr_ae (by filter_upwards with x using by rw [htop x])
  rw [← hbase', ← hmap]
  exact (integral_map (ChainSetup.measurable_coord k).aemeasurable
    ((measurable_norm.pow_const 2).aestronglyMeasurable)).symm

/-- **`∫ ‖ξ_k‖² = c²·dim`** at the chain's own step. -/
theorem integral_norm_step_sq (c : ℝ) (k : ℕ) :
    ∫ ω, ‖ChainSetup.step (ι := UT n) c k ω‖ ^ 2
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      = c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) := by
  have hfun : (fun ω => ‖ChainSetup.step (ι := UT n) c k ω‖ ^ 2)
      = fun ω => c ^ 2 * ‖ChainSetup.coord (F := EuclideanSpace ℝ (UT n)) k ω‖ ^ 2 := by
    funext ω
    rw [ChainSetup.step, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hfun, integral_const_mul, integral_norm_coord_sq]

/-- `min(x, c) ≥ x − x²/c` for `0 ≤ x` and `0 < c`. -/
theorem min_ge_sub_sq_div {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) : x - x ^ 2 / c ≤ min x c := by
  rcases le_total x c with h | h
  · rw [min_eq_left h]
    have : (0 : ℝ) ≤ x ^ 2 / c := by positivity
    linarith
  · rw [min_eq_right h]
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add']
    rw [le_div_iff₀ hc]
    nlinarith [hx, hc, h]

theorem integral_sqTrunc_ge {c cap : ℝ} (hcap : 0 < cap) (k : ℕ) :
    c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
        - 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 / cap
      ≤ ∫ ω, StepTruncVariance.sqTrunc (n := n) c cap k ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  classical
  set P := ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)) with hP
  have h4 := GaussianFourth.integral_norm_pow_four_le (n := n) c k
  have hcoord4 : Integrable (fun x : EuclideanSpace ℝ (UT n) => ‖x‖ ^ 4)
      (stdGaussian (EuclideanSpace ℝ (UT n))) := by
    have h := (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (UT n)))
      (4 : ℕ) (by simp)).integrable_norm_pow'
    simpa using h
  have h4c : Integrable (fun ω => ‖ChainSetup.coord (F := EuclideanSpace ℝ (UT n)) k ω‖ ^ 4) P := by
    rw [hP]
    refine (integrable_map_measure ((measurable_norm.pow_const 4)).aestronglyMeasurable
      (ChainSetup.measurable_coord k).aemeasurable).1 ?_
    rw [ChainSetup.map_coord]; exact hcoord4
  have h4i : Integrable (fun ω => ‖ChainSetup.step (ι := UT n) c k ω‖ ^ 4) P := by
    have hfun : (fun ω => ‖ChainSetup.step (ι := UT n) c k ω‖ ^ 4)
        = fun ω => |c| ^ 4 * ‖ChainSetup.coord (F := EuclideanSpace ℝ (UT n)) k ω‖ ^ 4 := by
      funext ω; rw [ChainSetup.step, norm_smul, Real.norm_eq_abs, mul_pow]
    rw [hfun]; exact h4c.const_mul _
  have h2i : Integrable (fun ω => ‖ChainSetup.step (ι := UT n) c k ω‖ ^ 2) P := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add h4i)
      (((ChainSetup.measurable_step c k).norm.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards with ω
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (‖ChainSetup.step (ι := UT n) c k ω‖ ^ 2 - 1),
      sq_nonneg (‖ChainSetup.step (ι := UT n) c k ω‖), norm_nonneg
        (ChainSetup.step (ι := UT n) c k ω), pow_le_pow_left₀ (norm_nonneg
        (ChainSetup.step (ι := UT n) c k ω)) (le_refl _) 2]
  have hpt : ∀ ω, ‖ChainSetup.step (ι := UT n) c k ω‖ ^ 2
      - (‖ChainSetup.step (ι := UT n) c k ω‖ ^ 2) ^ 2 / cap
      ≤ StepTruncVariance.sqTrunc (n := n) c cap k ω := fun ω =>
    min_ge_sub_sq_div (by positivity) hcap
  have hsub : Integrable (fun ω => ‖ChainSetup.step (ι := UT n) c k ω‖ ^ 2
      - (‖ChainSetup.step (ι := UT n) c k ω‖ ^ 2) ^ 2 / cap) P := by
    refine h2i.sub ?_
    have : (fun ω => (‖ChainSetup.step (ι := UT n) c k ω‖ ^ 2) ^ 2 / cap)
        = fun ω => ‖ChainSetup.step (ι := UT n) c k ω‖ ^ 4 / cap := by
      funext ω; rw [← pow_mul]
    rw [this]; exact h4i.div_const _
  have hTi : Integrable (StepTruncVariance.sqTrunc (n := n) c cap k) P := by
    refine Integrable.mono' (integrable_const cap)
      (StepTruncVariance.measurable_sqTrunc c cap k).aestronglyMeasurable ?_
    filter_upwards with ω
    have h := StepTruncVariance.sqTrunc_mem_Icc (n := n) (c := c) hcap.le k ω
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2
  have hmono := integral_mono hsub hTi hpt
  have hsplit : ∫ ω, (‖ChainSetup.step (ι := UT n) c k ω‖ ^ 2
        - (‖ChainSetup.step (ι := UT n) c k ω‖ ^ 2) ^ 2 / cap) ∂P
      = (∫ ω, ‖ChainSetup.step (ι := UT n) c k ω‖ ^ 2 ∂P)
        - (∫ ω, ‖ChainSetup.step (ι := UT n) c k ω‖ ^ 4 ∂P) / cap := by
    have hfun : (fun ω => (‖ChainSetup.step (ι := UT n) c k ω‖ ^ 2) ^ 2 / cap)
        = fun ω => ‖ChainSetup.step (ι := UT n) c k ω‖ ^ 4 / cap := by
      funext ω; rw [← pow_mul]
    rw [integral_sub h2i (by rw [hfun]; exact h4i.div_const _), hfun, integral_div]
  rw [hsplit, integral_norm_step_sq] at hmono
  have hdiv : (∫ ω, ‖ChainSetup.step (ι := UT n) c k ω‖ ^ 4 ∂P) / cap
      ≤ 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 / cap := by
    gcongr
  linarith

end D5.S3.Arith.Lattices.Klartag.Walk.StepSecondMoment
