/- GID: D5/S3/Quantum/PredictionDepth/MultiContextBudgetLowerBound
   generality: G
   mirror-B: D5/B/S3/Quantum/PredictionDepth/MultiContextBudgetLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete normalized contexts require d squared minus one independent outcomes. -/

import D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence
import Mathlib.LinearAlgebra.Dimension.Constructions

/- Library-search audit trail (2026-08-27):
   * Exact repository hits `traceZeroHermitian`, `trace_zero_hermitian_finrank`,
     and `informational_completeness_four_way` supply the real traceless carrier,
     its dimension, and the density-state-completeness bridge.
   * `CompleteContextTomography.complete_context_tomography` is the motivating
     complementary-context instance, but does not state the generic budget bound.
   * Exact pinned-Mathlib hits `Submodule.finrank_le_of_span_eq_top` and
     `Fintype.card_sigma` provide the finite spanning-family bound and its count.
   * No packaged generic multi-context informational budget theorem was found. -/

noncomputable section

open scoped BigOperators Matrix

namespace D5.S3.Quantum.PredictionDepth.MultiContextBudgetLowerBound

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- If context `x` has `independentCount x + 1` normalized outcomes and their
joint density-state readout is informationally complete, then the sum of the
independent outcome counts is at least the real traceless Hermitian dimension. -/
theorem multi_context_budget_lower_bound
    (d : Nat) [NeZero d]
    {Context : Type*} [Fintype Context]
    (independentCount : Context -> Nat)
    (effect : (x : Context) ->
      Fin (independentCount x + 1) -> traceZeroHermitian d)
    (hnormalized : forall x, ∑ j, effect x j = 0)
    (hcomplete : Function.Injective
      (fun rho : DensityState (Fin d) => fun x => fun j =>
        (Matrix.trace
          (CStarMatrix.ofMatrix.symm rho.1 * (effect x j).1.1)).re)) :
    d ^ 2 - 1 ≤ ∑ x, independentCount x := by
  classical
  let fullEffects : (Σ x, Fin (independentCount x + 1)) ->
      traceZeroHermitian d :=
    fun index => effect index.1 index.2
  have hfullComplete : Function.Injective
      (fun rho : DensityState (Fin d) => fun index =>
        (Matrix.trace
          (CStarMatrix.ofMatrix.symm rho.1 * (fullEffects index).1.1)).re) := by
    intro rho sigma hreadout
    apply hcomplete
    funext x j
    exact congrFun hreadout ⟨x, j⟩
  have hfullSpan :
      Submodule.span ℝ (Set.range fullEffects) = ⊤ :=
    ((informational_completeness_four_way d fullEffects).out 0 3).mp
      hfullComplete
  let reducedEffects : (Σ x, Fin (independentCount x)) ->
      traceZeroHermitian d :=
    fun index => effect index.1 index.2.castSucc
  have hreducedSpan :
      Submodule.span ℝ (Set.range reducedEffects) = ⊤ := by
    apply top_unique
    rw [← hfullSpan]
    apply Submodule.span_le.mpr
    rintro value ⟨⟨x, outcome⟩, rfl⟩
    change effect x outcome ∈ Submodule.span ℝ (Set.range reducedEffects)
    refine Fin.lastCases ?_ (fun j : Fin (independentCount x) => ?_) outcome
    · have hsum := hnormalized x
      rw [Fin.sum_univ_castSucc] at hsum
      have hlast : effect x (Fin.last (independentCount x)) =
          -∑ j : Fin (independentCount x), effect x j.castSucc := by
        rw [eq_neg_iff_add_eq_zero]
        simpa [add_comm] using hsum
      rw [hlast]
      apply Submodule.neg_mem
      apply Submodule.sum_mem
      intro j _
      apply Submodule.subset_span
      exact ⟨⟨x, j⟩, rfl⟩
    · apply Submodule.subset_span
      exact ⟨⟨x, j⟩, rfl⟩
  calc
    d ^ 2 - 1 = Module.finrank ℝ (traceZeroHermitian d) :=
      (trace_zero_hermitian_finrank d).symm
    _ ≤ Fintype.card (Σ x, Fin (independentCount x)) :=
      finrank_le_of_span_eq_top hreducedSpan
    _ = ∑ x, independentCount x := by
      rw [Fintype.card_sigma]
      simp

#print axioms multi_context_budget_lower_bound

end D5.S3.Quantum.PredictionDepth.MultiContextBudgetLowerBound
