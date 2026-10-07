/- GID: D5/S3/Arith/Lattices/Klartag/Walk/StepInputs
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/StepInputs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Walk.Increments
import D5.S3.Arith.Lattices.Klartag.Completion.GoodEvent

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Walk.StepInputs

open MeasureTheory
open ProbabilityTheory
open Module
open Set
open Finset
open scoped ENNReal NNReal RealInnerProductSpace

section Moments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A continuous linear functional is square-integrable for a standard Gaussian. -/
theorem memLp_dual (L : StrongDual ℝ E) : MemLp (fun x => L x) 2 (stdGaussian E) := by
  have h1 : MemLp (fun x : E => ‖L‖ * ‖x‖) 2 (stdGaussian E) :=
    (IsGaussian.memLp_two_id.norm).const_mul ‖L‖
  refine MemLp.mono h1 (L.continuous.aestronglyMeasurable) ?_
  filter_upwards with x
  calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
    _ = ‖‖L‖ * ‖x‖‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- The second moment of a linear functional under a standard Gaussian is `‖L‖²`. -/
theorem integral_sq_dual (L : StrongDual ℝ E) :
    ∫ x, (L x) ^ 2 ∂(stdGaussian E) = ‖L‖ ^ 2 := by
  have hV := variance_dual_stdGaussian (E := E) L
  rw [variance_eq_sub (memLp_dual L)] at hV
  have h0 : (stdGaussian E)[fun x => L x] = 0 := integral_strongDual_stdGaussian L
  simp only [h0] at hV
  simpa using hV

omit [MeasurableSpace E] [BorelSpace E] in
/-- `‖π x‖²` expanded in an orthonormal basis of the range, with the projection removed. -/
theorem norm_sq_starProjection_eq_sum (K : Submodule ℝ E) [K.HasOrthogonalProjection] (x : E) :
    ‖K.starProjection x‖ ^ 2 = ∑ i, ⟪x, ((stdOrthonormalBasis ℝ K) i : E)⟫ ^ 2 := by
  set b := stdOrthonormalBasis ℝ K
  have hmem := K.starProjection_apply_mem x
  have h1 := (b.sum_sq_inner_left (⟨K.starProjection x, hmem⟩ : K)).symm
  rw [show ‖(⟨K.starProjection x, hmem⟩ : K)‖ = ‖K.starProjection x‖ from rfl] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hbi : ((b i : K) : E) ∈ K := (b i).2
  have hc : ⟪(⟨K.starProjection x, hmem⟩ : K), b i⟫ = ⟪K.starProjection x, ((b i : K) : E)⟫ := rfl
  rw [hc, K.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hbi]

theorem integral_norm_sq_starProjection (K : Submodule ℝ E) [K.HasOrthogonalProjection] :
    ∫ x, ‖K.starProjection x‖ ^ 2 ∂(stdGaussian E) = (Module.finrank ℝ K : ℝ) := by
  classical
  set b := stdOrthonormalBasis ℝ K with hb
  have hL : ∀ (i : Fin (Module.finrank ℝ K)) (x : E),
      ⟪x, ((b i : K) : E)⟫ = (innerSL ℝ ((b i : K) : E)) x := fun i x => real_inner_comm _ _
  have hnorm : ∀ i : Fin (Module.finrank ℝ K), ‖((b i : K) : E)‖ = 1 := by
    intro i
    rw [show ‖((b i : K) : E)‖ = ‖(b i : K)‖ from rfl]
    exact b.norm_eq_one i
  have hint : ∀ i : Fin (Module.finrank ℝ K),
      Integrable (fun x : E => ⟪x, ((b i : K) : E)⟫ ^ 2) (stdGaussian E) := by
    intro i
    refine ((memLp_dual (innerSL ℝ ((b i : K) : E))).integrable_sq).congr ?_
    filter_upwards with x
    rw [hL i x]
  have hsq : ∀ i : Fin (Module.finrank ℝ K),
      ∫ x, ⟪x, ((b i : K) : E)⟫ ^ 2 ∂(stdGaussian E) = 1 := by
    intro i
    have h1 : ∫ x, ⟪x, ((b i : K) : E)⟫ ^ 2 ∂(stdGaussian E)
        = ∫ x, ((innerSL ℝ ((b i : K) : E)) x) ^ 2 ∂(stdGaussian E) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show ⟪x, ((b i : K) : E)⟫ ^ 2 = _
      rw [hL i x]
    rw [h1, integral_sq_dual, innerSL_apply_norm, hnorm i, one_pow]
  calc ∫ x, ‖K.starProjection x‖ ^ 2 ∂(stdGaussian E)
      = ∫ x, ∑ i, ⟪x, ((b i : K) : E)⟫ ^ 2 ∂(stdGaussian E) :=
        integral_congr_ae (Filter.Eventually.of_forall (norm_sq_starProjection_eq_sum K))
    _ = ∑ i, ∫ x, ⟪x, ((b i : K) : E)⟫ ^ 2 ∂(stdGaussian E) :=
        integral_finsetSum _ (fun i _ => hint i)
    _ = (Module.finrank ℝ K : ℝ) := by
        rw [Finset.sum_congr rfl fun i _ => hsq i]
        simp

end Moments

section Conditional

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α : Type*} [mα : MeasurableSpace α]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [mE : MeasurableSpace E] [BorelSpace E]

end Conditional

section Good

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}

def goodEventUT (r : ℝ) (ξ : Ω → EuclideanSpace ℝ (Increments.UT n)) (thr : ℝ) : Set Ω :=
  {ω | ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (r • Increments.symMat (ξ ω))‖ ≤ thr}

theorem measureReal_compl_goodEventUT_le {r : ℝ} (hr : 0 < r)
    {ξ : Ω → EuclideanSpace ℝ (Increments.UT n)} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ (Increments.UT n)))
    (s : ℝ) (hs : 1 ≤ s) :
    P.real (goodEventUT r ξ (6 * r * s * Real.sqrt n))ᶜ ≤ 4 * Real.exp (-(s ^ 2 * n)) := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top P _))
    (Increments.increment_opNorm_tail hr hξ hlaw s hs)
  intro ω hω
  have hω' : ¬ (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (r • Increments.symMat (ξ ω))‖
      ≤ 6 * r * s * Real.sqrt n) := hω
  exact le_of_lt (not_le.mp hω')

end Good

section H1

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : Type*} [mα : MeasurableSpace α]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [mE : MeasurableSpace E] [BorelSpace E]

end H1

end D5.S3.Arith.Lattices.Klartag.Walk.StepInputs
