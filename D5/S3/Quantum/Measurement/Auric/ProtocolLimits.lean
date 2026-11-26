/- GID: D5/S3/Quantum/Measurement/Auric/ProtocolLimits
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/ProtocolLimits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Classical randomization and almost-sure stopping of projective protocols. -/

import D5.S3.Quantum.Measurement.Auric.DiamondClosure
import D5.S3.Analytic.Convexity.MeasurableFiniteMoments
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Order

/-! # Classical randomization and almost-sure stopping of projective protocols -/

namespace D5.S3.Quantum.Measurement.Auric.ProtocolLimits

open _root_.Matrix Filter MeasureTheory D5.S3.Quantum.Foundation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Measurement.Auric.ExactDistance
open D5.S3.Quantum.Measurement.Auric.DiamondClosure
open D5.S3.Quantum.Measurement.Auric.DiamondBounds
open D5.S3.Quantum.Measurement.Auric.ProjectiveTree (Protocol)
open D5.S3.Quantum.Measurement.Auric.ScoreReadout (protocolMap)
open D5.S3.Quantum.Measurement.Auric.SimulatorUpper
open scoped ComplexOrder MatrixOrder Topology Matrix.Norms.Elementwise

noncomputable section

local instance matrixContinuousENorm (ι : Type*) [Fintype ι] :
    ContinuousENorm (Matrix ι ι ℂ) := inferInstanceAs (ContinuousENorm (ι → ι → ℂ))

/-- An input-independent probability law of finite trees gives exactly a finite
convex combination of trees drawn from the same family. -/
theorem finite_of_randomized_trees {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Ω → Protocol Level) (F : RecordedMap)
    (hp : Integrable (fun ω => (protocolMap (p ω)).choi_matrix) μ)
    (hF : F.choi_matrix = ∫ ω, (protocolMap (p ω)).choi_matrix ∂μ) :
    FiniteProtocolMixture F := by
  obtain ⟨m, w, ω, hw, hw1, _, hsum⟩ :=
    D5.S3.Analytic.Convexity.MeasurableFiniteMoments.finite_moments_probability μ hp
      (s := Set.univ) (.of_forall fun _ => Set.mem_univ _)
  refine ⟨m, p ∘ ω, w, hw, hw1, MatrixMap.choi_matrix_inj ?_⟩
  rw [hF, ← hsum]
  ext ⟨i, s⟩ ⟨j, t⟩
  simp only [MatrixMap.choi_matrix, LinearMap.sum_apply, LinearMap.smul_apply,
    Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, Function.comp_apply]
  rfl

private noncomputable def traceReplace (c : ℝ) : RecordedMap where
  toFun X := ((c : ℂ) * X.trace) • (1 : Matrix (Flag × Level) (Flag × Level) ℂ)
  map_add' X Y := by simp [Matrix.trace_add, mul_add, add_smul]
  map_smul' u X := by simp [Matrix.trace_smul, smul_smul, mul_left_comm]

private theorem choi_traceReplace (c : ℝ) :
    (traceReplace c).choi_matrix = c • (1 : Matrix FlaggedCoord FlaggedCoord ℂ) := by
  ext ⟨i, s⟩ ⟨j, t⟩
  simp only [traceReplace, MatrixMap.choi_matrix, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, Complex.real_smul,
    smul_eq_mul]
  by_cases h : s = t
  · subst t
    simp [Matrix.trace_single_eq_same]
  · simp [Matrix.trace_single_eq_of_ne s t (1 : ℂ) h, h]

private theorem trace_traceReplace (c : ℝ) (X : Matrix Level Level ℂ) :
    (traceReplace c X).trace = ((10 * c : ℝ) : ℂ) * X.trace := by
  change (((c : ℂ) * X.trace) • (1 : Matrix (Flag × Level) (Flag × Level) ℂ)).trace = _
  rw [Matrix.trace_smul, Matrix.trace_one]
  norm_num [Fintype.card_prod, Fintype.card_fin]
  ring

private theorem choi_trace_eq (F : RecordedMap) : F.choi_matrix.trace = (F 1).trace := by
  have hsum : ∑ s : Level, Matrix.single s s (1 : ℂ) = 1 := by
    ext s t
    simp [Matrix.sum_apply, Matrix.single, Matrix.one_apply, eq_comm, ite_and]
  calc
    _ = ∑ s : Level, (F (Matrix.single s s 1)).trace := by
      unfold Matrix.trace Matrix.diag
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    _ = _ := by rw [← Matrix.trace_sum, ← map_sum, hsum]

/-- The trace of the unfinished operation on the identity bounds the diamond
error made by replacing that continuation, uniformly in the reference. -/
theorem stopped_tail_diamond_bound (F G D : RecordedMap)
    (hF : F.IsTracePreserving) (hG : G.IsTracePreserving)
    (hFD : (F - D).IsCompletelyPositive) (hGD : (G - D).IsCompletelyPositive) :
    DiamondBound (F - G) (20 * ((F - D) 1).trace.re) := by
  let c : ℝ := ((F - D) 1).trace.re
  have hP := (MatrixMap.choi_PSD_iff_CP_map (F - D)).mp hFD
  let J : HermitianMat FlaggedCoord ℂ := ⟨_, hP.isHermitian⟩
  have hJ := HermitianMat.le_trace_smul_one
    (HermitianMat.zero_le_iff.mpr hP : 0 ≤ J)
  change (F - D).choi_matrix ≤ (F - D).choi_matrix.trace.re • 1 at hJ
  rw [choi_trace_eq] at hJ
  have hc : 0 ≤ c := by
    change 0 ≤ ((F - D) 1).trace.re
    rw [← choi_trace_eq]
    exact (RCLike.nonneg_iff.mp hP.trace_nonneg).1
  have hcp : (traceReplace c).IsCompletelyPositive := by
    rw [MatrixMap.choi_PSD_iff_CP_map, choi_traceReplace]
    exact Matrix.PosSemidef.one.smul hc
  have hdom : (traceReplace c - (F - D)).IsCompletelyPositive := by
    rw [MatrixMap.choi_PSD_iff_CP_map]
    change ((traceReplace c).choi_matrix - (F - D).choi_matrix).PosSemidef
    rw [choi_traceReplace]
    exact Matrix.le_iff.mp hJ
  have hmajor : (traceReplace c - (F - G)).IsCompletelyPositive := by
    rw [show traceReplace c - (F - G) =
      (traceReplace c - (F - D)) + (G - D) by abel]
    exact hdom.add hGD
  intro R _ _ X
  have h := amplified_traceNorm_le_of_completelyPositive_majorant (F - G)
    (traceReplace c) (10 * c) hcp hmajor
    (fun Y => by rw [LinearMap.sub_apply, Matrix.trace_sub, hF Y, hG Y, sub_self])
    (trace_traceReplace c) (r := R) X
  rw [show (2 : ℝ) * (10 * c) = 20 * c by ring] at h
  exact h

/-- A normalized channel with legal finite truncations belongs to the diamond
closure if the probability of still running on the maximally mixed state
vanishes. `done n` is the common operation of histories already stopped at `n`. -/
theorem inClosure_of_almost_sure_truncations (F : RecordedMap) (hF : F.IsTracePreserving)
    (truncated done : ℕ → RecordedMap)
    (htruncated : ∀ n, FiniteProtocolMixture (truncated n))
    (hcontinuation : ∀ n, (F - done n).IsCompletelyPositive)
    (hforcedStop : ∀ n, (truncated n - done n).IsCompletelyPositive)
    (hhalt : Tendsto (fun n => ((F - done n) 1).trace.re) atTop (𝓝 0)) :
    ProtocolClosure F := by
  intro ε hε
  have htail : ∀ᶠ n in atTop, ((F - done n) 1).trace.re < ε / 20 :=
    hhalt.eventually_lt_const (by positivity)
  obtain ⟨n, hn⟩ := htail.exists
  refine ⟨truncated n, htruncated n, fun R _ _ X => ?_⟩
  apply (stopped_tail_diamond_bound F (truncated n) (done n) hF
    (FiniteProtocolMixture.tp (htruncated n)) (hcontinuation n) (hforcedStop n) R X).trans
  exact mul_le_mul_of_nonneg_right (by linarith) (FiniteTraceDistance.traceNorm_nonneg X)

end

end D5.S3.Quantum.Measurement.Auric.ProtocolLimits
