/- GID: D5/S3/CompletionDynamics/DynamicReal/CompletionThreadNonreconstruction
   generality: I
   mirror-B: D5/B/S3/CompletionDynamics/DynamicReal/CompletionThreadNonreconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden threads share one completion while controlled completion remains canonically minimal. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenThreadBlowup
import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/- Library-search audit trail (2026-09-02):
   * Repository name and body-shape searches found the canonical
     `goldenGeometricThread`, `controlledBehavior`, and `ControlledCompletion`
     objects; all are imported rather than redeclared.
   * The frozen `CompletionThreadFiber` module defines completion to be a
     constant on an auxiliary observer carrier, so it is not an exact hit for
     the source's convergent real-thread completion map.
   * Exact repository hit `controlled_behavior_universal_property` supplies
     the finite controlled quotient's unique surjective factor and cardinal
     minimality, and is applied directly.
   * Exact pinned-Mathlib hits
     `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` and
     `Filter.Tendsto.limUnder_eq` identify the completed value of the genuine
     geometric threads. Repository and pinned-Mathlib searches found no theorem
     already combining those thread clauses with controlled minimality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.DynamicReal.CompletionThreadNonreconstruction

open Filter
open scoped Topology goldenRatio
open D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap
open D5.S3.CompletionDynamics.GoldenMobius.GoldenCrossRatioLinearization
open D5.S3.CompletionDynamics.GoldenMobius.GoldenProjectiveDerivative
open D5.S3.CompletionDynamics.GoldenMobius.GoldenThreadBlowup
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- Every golden geometric thread converges to the same completed value. The
completion is not injective on the actual range of thread functions, and no
completed-value decoder recovers every origin coefficient. Independently, the
canonical finite-word controlled completion retains its universal minimal
realization property. -/
theorem completion_thread_nonreconstruction :
    (forall c : ℝ,
      Tendsto (goldenGeometricThread c) atTop (nhds Real.goldenRatio) /\
        Filter.limUnder atTop (goldenGeometricThread c) = Real.goldenRatio) /\
    (Not (Function.Injective
      (fun thread : Set.range goldenGeometricThread =>
        Filter.limUnder atTop thread.1))) /\
    (Not (exists decode : ℝ -> ℝ,
      forall c : ℝ,
        decode (Filter.limUnder atTop (goldenGeometricThread c)) = c)) /\
    (forall {Y U O W : Type*} [Fintype Y] [Fintype W]
      (update : U -> Y -> Y) (readout : Y -> O)
      (realization : Y -> W) (realizedUpdate : U -> W -> W)
      (realizedReadout : W -> O),
      Function.Surjective realization ->
      (forall u, realization ∘ update u = realizedUpdate u ∘ realization) ->
      readout = realizedReadout ∘ realization ->
      (ExistsUnique fun factor : W -> ControlledCompletion update readout =>
        Function.Surjective factor /\
          completionProjection update readout = factor ∘ realization /\
          (forall u, factor ∘ realizedUpdate u =
            completionUpdate update readout u ∘ factor) /\
          completionReadout update readout ∘ factor = realizedReadout) /\
        Fintype.card (ControlledCompletion update readout) <= Fintype.card W) := by
  have threadTendsto : forall c : ℝ,
      Tendsto (goldenGeometricThread c) atTop (nhds Real.goldenRatio) := by
    intro c
    have multiplierTendsto :
        Tendsto (fun n : ℕ => goldenProjectiveMultiplier ^ n) atTop (nhds 0) := by
      apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      simpa [Real.norm_eq_abs] using abs_golden_projective_multiplier_lt_one
    change Tendsto
      ((goldenThreadCurve c) ∘ fun n : ℕ => goldenProjectiveMultiplier ^ n)
      atTop (nhds Real.goldenRatio)
    simpa only [golden_thread_curve_zero] using
      (golden_thread_curve_hasDerivAt c).continuousAt.tendsto.comp multiplierTendsto
  have completionValue : forall c : ℝ,
      Filter.limUnder atTop (goldenGeometricThread c) = Real.goldenRatio := by
    intro c
    exact (threadTendsto c).limUnder_eq
  refine ⟨fun c => ⟨threadTendsto c, completionValue c⟩, ?_, ?_, ?_⟩
  · intro injectiveCompletion
    let first : Set.range goldenGeometricThread :=
      ⟨goldenGeometricThread 0, ⟨0, rfl⟩⟩
    let second : Set.range goldenGeometricThread :=
      ⟨goldenGeometricThread 2, ⟨2, rfl⟩⟩
    have sameCompletion :
        Filter.limUnder atTop first.1 = Filter.limUnder atTop second.1 := by
      simp only [first, second, completionValue]
    have sameThread := congrArg Subtype.val (injectiveCompletion sameCompletion)
    have sameAtZero := congrFun sameThread 0
    have sameCrossRatio := congrArg goldenCrossRatio sameAtZero
    rw [golden_geometric_thread_cross_ratio (c := 0) (n := 0) (by norm_num),
      golden_geometric_thread_cross_ratio (c := 2) (n := 0) (by norm_num)] at sameCrossRatio
    norm_num at sameCrossRatio
  · rintro ⟨decode, recovers⟩
    have recoversZero := recovers 0
    have recoversTwo := recovers 2
    rw [completionValue 0] at recoversZero
    rw [completionValue 2] at recoversTwo
    linarith
  · intro Y U O W instY instW update readout realization realizedUpdate
      realizedReadout realizationSurjective updatesCommute readoutsCommute
    exact controlled_behavior_universal_property update readout realization
      realizedUpdate realizedReadout realizationSurjective updatesCommute
      readoutsCommute

#print axioms completion_thread_nonreconstruction

end D5.S3.CompletionDynamics.DynamicReal.CompletionThreadNonreconstruction
