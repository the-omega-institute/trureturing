/- GID: D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyTriangle
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyTriangle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One-way finite experiment deficiency satisfies the triangle inequality. -/

import D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer

/- Library-search audit trail (2026-08-28):
   * The imported module supplies the canonical finite experiment deficiency;
     it is reused rather than redeclared.
   * `TotalVariation.Metric.total_variation_triangle` and
     `TotalVariation.DataProcessing.total_variation_channel_le` are the exact
     metric and contraction components used below.
   * Pinned Mathlib and D5 searches found no exact whole-theorem hit for the
     infimum over two independently chosen stochastic simulators. -/

noncomputable section

open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyTriangle

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open D5.S3.TotalVariation.DataProcessing
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

/-- Composing approximate simulators and using total-variation contraction
gives the triangle inequality for one-way finite deficiency. -/
theorem finite_deficiency_triangle
    {State FirstObservation MiddleObservation FinalObservation : Type*}
    [Fintype State] [Nonempty State]
    [Fintype FirstObservation] [Fintype MiddleObservation]
    [Fintype FinalObservation]
    (first : FiniteMarkovKernel State FirstObservation)
    (middle : FiniteMarkovKernel State MiddleObservation)
    (final : FiniteMarkovKernel State FinalObservation) :
    finiteDeficiency final.1 first.1 ≤
      finiteDeficiency final.1 middle.1 +
        finiteDeficiency middle.1 first.1 := by
  unfold finiteDeficiency
  apply ENNReal.le_iInf_add_iInf
  intro middleToFinal firstToMiddle
  let composite : FirstObservation → FinalObservation → Real :=
    fun observation output =>
      channelOutput middleToFinal.1 (firstToMiddle.1 observation) output
  have compositeStochastic : IsRowStochastic composite := by
    constructor
    · intro observation output
      unfold composite channelOutput
      exact Finset.sum_nonneg fun intermediate _ =>
        mul_nonneg (firstToMiddle.2.1 observation intermediate)
          (middleToFinal.2.1 intermediate output)
    · intro observation
      unfold composite channelOutput
      calc
        (∑ output, ∑ intermediate,
            firstToMiddle.1 observation intermediate *
              middleToFinal.1 intermediate output) =
            ∑ intermediate, ∑ output,
              firstToMiddle.1 observation intermediate *
                middleToFinal.1 intermediate output := Finset.sum_comm
        _ = ∑ intermediate,
            firstToMiddle.1 observation intermediate *
              ∑ output, middleToFinal.1 intermediate output := by
          apply Finset.sum_congr rfl
          intro intermediate _
          rw [Finset.mul_sum]
        _ = ∑ intermediate, firstToMiddle.1 observation intermediate := by
          apply Finset.sum_congr rfl
          intro intermediate _
          rw [middleToFinal.2.2 intermediate, mul_one]
        _ = 1 := firstToMiddle.2.2 observation
  let compositeKernel : FiniteMarkovKernel FirstObservation FinalObservation :=
    ⟨composite, compositeStochastic⟩
  have composedOutput (mass : FirstObservation → Real) :
      channelOutput composite mass =
        channelOutput middleToFinal.1
          (channelOutput firstToMiddle.1 mass) := by
    funext output
    unfold composite channelOutput
    calc
      (∑ observation, mass observation *
          ∑ intermediate,
            firstToMiddle.1 observation intermediate *
              middleToFinal.1 intermediate output) =
          ∑ observation, ∑ intermediate,
            (mass observation * firstToMiddle.1 observation intermediate) *
              middleToFinal.1 intermediate output := by
        apply Finset.sum_congr rfl
        intro observation _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro intermediate _
        ring
      _ = ∑ intermediate, ∑ observation,
          (mass observation * firstToMiddle.1 observation intermediate) *
            middleToFinal.1 intermediate output := Finset.sum_comm
      _ = ∑ intermediate,
          (∑ observation,
            mass observation * firstToMiddle.1 observation intermediate) *
              middleToFinal.1 intermediate output := by
        apply Finset.sum_congr rfl
        intro intermediate _
        rw [Finset.sum_mul]
  have compositeError :
      uniformSimulationError final.1 first.1 compositeKernel ≤
        uniformSimulationError final.1 middle.1 middleToFinal +
          uniformSimulationError middle.1 first.1 firstToMiddle := by
    unfold uniformSimulationError
    apply Finset.sup'_le
    intro state _
    rw [composedOutput]
    calc
      totalVariation (final.1 state)
          (channelOutput middleToFinal.1
            (channelOutput firstToMiddle.1 (first.1 state))) ≤
          totalVariation (final.1 state)
              (channelOutput middleToFinal.1 (middle.1 state)) +
            totalVariation
              (channelOutput middleToFinal.1 (middle.1 state))
              (channelOutput middleToFinal.1
                (channelOutput firstToMiddle.1 (first.1 state))) :=
        total_variation_triangle _ _ _
      _ ≤ totalVariation (final.1 state)
              (channelOutput middleToFinal.1 (middle.1 state)) +
            totalVariation (middle.1 state)
              (channelOutput firstToMiddle.1 (first.1 state)) :=
        add_le_add le_rfl
          (total_variation_channel_le
            (middle.1 state)
            (channelOutput firstToMiddle.1 (first.1 state))
            middleToFinal.1 middleToFinal.2)
      _ ≤ Finset.univ.sup' Finset.univ_nonempty
              (fun candidate => totalVariation (final.1 candidate)
                (channelOutput middleToFinal.1 (middle.1 candidate))) +
            Finset.univ.sup' Finset.univ_nonempty
              (fun candidate => totalVariation (middle.1 candidate)
                (channelOutput firstToMiddle.1 (first.1 candidate))) :=
        add_le_add
          (Finset.le_sup'
            (fun candidate : State => totalVariation (final.1 candidate)
              (channelOutput middleToFinal.1 (middle.1 candidate)))
            (Finset.mem_univ state))
          (Finset.le_sup'
            (fun candidate : State => totalVariation (middle.1 candidate)
              (channelOutput firstToMiddle.1 (first.1 candidate)))
            (Finset.mem_univ state))
  calc
    (⨅ simulator : FiniteMarkovKernel FirstObservation FinalObservation,
        ENNReal.ofReal
          (uniformSimulationError final.1 first.1 simulator)) ≤
        ENNReal.ofReal
          (uniformSimulationError final.1 first.1 compositeKernel) :=
      iInf_le _ compositeKernel
    _ ≤ ENNReal.ofReal
        (uniformSimulationError final.1 middle.1 middleToFinal +
          uniformSimulationError middle.1 first.1 firstToMiddle) :=
      ENNReal.ofReal_le_ofReal compositeError
    _ ≤ ENNReal.ofReal
          (uniformSimulationError final.1 middle.1 middleToFinal) +
        ENNReal.ofReal
          (uniformSimulationError middle.1 first.1 firstToMiddle) :=
      ENNReal.ofReal_add_le

#print axioms finite_deficiency_triangle

end D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyTriangle
