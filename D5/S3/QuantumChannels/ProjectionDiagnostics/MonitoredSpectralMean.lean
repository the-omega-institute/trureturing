/- GID: D5/S3/QuantumChannels/ProjectionDiagnostics/MonitoredSpectralMean
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/ProjectionDiagnostics/MonitoredSpectralMean
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Finite dimensional monitored return and the occupied cyclic spectrum. -/

import D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredPowerBound
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.MonotoneConvergence

noncomputable section
open scoped InnerProductSpace BigOperators
open InnerProductSpace Filter Topology

namespace D5.S3.QuantumChannels.ProjectionDiagnostics.MonitoredSpectralMean

open MonitoredReturnConservation CyclicMonitoredContraction CyclicMonitoredPowerBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

private def initial (U : E ≃ₗᵢ[ℂ] E) (v : E) : cyclicSpace U v :=
  ⟨v, initial_mem U v⟩

private def cyclicUnitary (U : E ≃ₗᵢ[ℂ] E) (v : E) :
    cyclicSpace U v ≃ₗᵢ[ℂ] cyclicSpace U v :=
  let f : cyclicSpace U v →ₗᵢ[ℂ] cyclicSpace U v :=
    { toLinearMap := U.toLinearMap.restrict (unitary_mem U v)
      norm_map' := fun x => U.norm_map (x : E) }
  LinearIsometryEquiv.ofSurjective f (LinearMap.surjective_of_injective f.injective)

private theorem unitary_coe (U : E ≃ₗᵢ[ℂ] E) (v : E) (x : cyclicSpace U v) :
    (cyclicUnitary U v x : E) = U (x : E) := rfl

private theorem step_factor (U : E ≃ₗᵢ[ℂ] E) (v : E) (hv : ‖v‖ = 1) :
    cyclicStep U v =
      (1 - rankOne ℂ (initial U v) (initial U v)) *
        (cyclicUnitary U v : cyclicSpace U v →L[ℂ] cyclicSpace U v) := by
  ext x
  apply Subtype.ext
  change U (x : E) - (ℂ ∙ v).starProjection (U (x : E)) =
    U (x : E) - (inner ℂ v (U (x : E))) • v
  rw [Submodule.starProjection_singleton, hv]
  simp

private theorem right_defect (U : E ≃ₗᵢ[ℂ] E) (v : E) (hv : ‖v‖ = 1) :
    1 - cyclicStep U v * star (cyclicStep U v) =
      rankOne ℂ (initial U v) (initial U v) := by
  let P := rankOne ℂ (initial U v) (initial U v)
  let W : cyclicSpace U v →L[ℂ] cyclicSpace U v := cyclicUnitary U v
  have hP : star P = P := by simp [P, ContinuousLinearMap.star_eq_adjoint]
  have hPP : P * P = P := by
    ext x
    simp [P, mul_apply_eq_comp, inner_self_eq_norm_sq_to_K, initial, hv]
  have hWW : W * star W = 1 := by
    ext x
    simp [W, mul_apply_eq_comp]
  rw [step_factor U v hv]
  change 1 - ((1 - P) * W) * star ((1 - P) * W) = P
  rw [star_mul, star_sub, star_one, hP]
  calc
    1 - ((1 - P) * W) * (star W * (1 - P)) =
        1 - (1 - P) * (W * star W) * (1 - P) := by noncomm_ring
    _ = P := by rw [hWW]; noncomm_ring [hPP]

private theorem gramian_telescope (U : E ≃ₗᵢ[ℂ] E) (v : E) (hv : ‖v‖ = 1)
    (H : ℕ) :
    (∑ n ∈ Finset.range H,
      rankOne ℂ ((cyclicStep U v ^ n) (initial U v))
        ((cyclicStep U v ^ n) (initial U v))) =
      1 - cyclicStep U v ^ H * star (cyclicStep U v ^ H) := by
  let A := cyclicStep U v
  have hterm (n : ℕ) :
      rankOne ℂ ((A ^ n) (initial U v)) ((A ^ n) (initial U v)) =
        A ^ n * star (A ^ n) - A ^ (n + 1) * star (A ^ (n + 1)) := by
    calc
      _ = A ^ n * rankOne ℂ (initial U v) (initial U v) * star (A ^ n) := by
        rw [ContinuousLinearMap.mul_def, comp_rankOne, ContinuousLinearMap.mul_def,
          rankOne_comp]
        simp [ContinuousLinearMap.star_eq_adjoint]
      _ = _ := by rw [← right_defect U v hv, pow_succ, star_mul]; noncomm_ring
  simp_rw [hterm]
  rw [Finset.sum_range_sub']
  simp

private theorem trace_survival (U : E ≃ₗᵢ[ℂ] E) (v : E) (hv : ‖v‖ = 1)
    (H : ℕ) :
    ∑ n ∈ Finset.range H, survivalProbability U v n =
      (Module.finrank ℂ (cyclicSpace U v) : ℝ) -
        (LinearMap.trace ℂ (cyclicSpace U v)
          ((cyclicStep U v ^ H * star (cyclicStep U v ^ H)).toLinearMap)).re := by
  have h := congrArg
    (fun X : cyclicSpace U v →L[ℂ] cyclicSpace U v =>
      (LinearMap.trace ℂ (cyclicSpace U v) X.toLinearMap).re)
    (gramian_telescope U v hv H)
  simpa [map_sum, map_sub, ContinuousLinearMap.toLinearMap_sum,
    ContinuousLinearMap.toLinearMap_sub, trace_rankOne,
    inner_self_eq_norm_sq_to_K, step_pow_coe, initial,
    survivalProbability, monitoredHistory] using h

private theorem weighted_finite (U : E ≃ₗᵢ[ℂ] E) (v : E) (hv : ‖v‖ = 1)
    (H : ℕ) :
    ∑ n ∈ Finset.range H, (n + 1 : ℝ) * returnProbability U v (n + 1) =
      (∑ n ∈ Finset.range H, survivalProbability U v n) -
        H * survivalProbability U v H := by
  have hp := (monitored_return_conservation U v hv).2.1
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hp H]
    push_cast
    ring

end D5.S3.QuantumChannels.ProjectionDiagnostics.MonitoredSpectralMean
