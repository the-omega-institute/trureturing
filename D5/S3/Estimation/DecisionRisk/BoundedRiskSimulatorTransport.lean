/- GID: D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Simulator error bounds statewise risk for every bounded-loss decision rule. -/

import D5.S3.Estimation.DecisionRisk.DescentDefectBounds

/- Library-search audit trail (2026-08-25):
   * All existing `Estimation/DecisionRisk` modules were checked. The Blackwell
     theorem treats exact garbling and optimal Bayes risk, while the descent
     modules treat quotient kernels; none states the approximate statewise
     risk transfer below.
   * Exact repository primitives `IsRowStochastic`, `channelOutput`, and
     `totalVariation` provide the finite kernels, their composition, and the
     source's probability-theory normalization. They are imported rather than
     redeclared.
   * Pinned Mathlib searches for bounded expectations against total variation
     and decision-risk stability found no exact whole-theorem hit. The proof
     applies `total_variation_eq_sum_positive` and finite-sum order lemmas. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DecisionRisk.BoundedRiskSimulatorTransport

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

private theorem bounded_expectation_le_add_total_variation
    {Index : Type*} [Fintype Index]
    (p q value : Index → Real)
    (sameMass : (∑ i, p i) = ∑ i, q i)
    (valueNonnegative : ∀ i, 0 ≤ value i)
    (valueAtMostOne : ∀ i, value i ≤ 1) :
    (∑ i, q i * value i) ≤
      (∑ i, p i * value i) + totalVariation p q := by
  classical
  have splitDifference :
      (∑ i, q i * value i) - ∑ i, p i * value i =
        ∑ i, (q i - p i) * value i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have discardNonpositive :
      (∑ i, (q i - p i) * value i) ≤
        ∑ i with p i ≤ q i, (q i - p i) * value i := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => p i ≤ q i) (fun i => (q i - p i) * value i)]
    have nonpositivePart :
        (∑ i with ¬p i ≤ q i, (q i - p i) * value i) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i member
      exact mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (le_of_not_ge (Finset.mem_filter.mp member).2))
        (valueNonnegative i)
    linarith
  have positivePart :
      (∑ i with p i ≤ q i, (q i - p i) * value i) ≤
        ∑ i with p i ≤ q i, (q i - p i) := by
    apply Finset.sum_le_sum
    intro i member
    have differenceNonnegative : 0 ≤ q i - p i :=
      sub_nonneg.mpr (Finset.mem_filter.mp member).2
    nlinarith [valueAtMostOne i]
  have positivePartIsVariation :
      (∑ i with p i ≤ q i, (q i - p i)) = totalVariation p q := by
    calc
      (∑ i with p i ≤ q i, (q i - p i)) = totalVariation q p :=
        (total_variation_eq_sum_positive q p sameMass.symm).symm
      _ = totalVariation p q := total_variation_comm q p
  linarith [splitDifference, discardNonpositive.trans
    (positivePart.trans_eq positivePartIsVariation)]

private theorem row_stochastic_channel_comp
    {Input Middle Output : Type*} [Fintype Middle] [Fintype Output]
    (first : Input → Middle → Real) (second : Middle → Output → Real)
    (firstStochastic : IsRowStochastic first)
    (secondStochastic : IsRowStochastic second) :
    IsRowStochastic
      (fun input output => channelOutput second (first input) output) := by
  constructor
  · intro input output
    simp only [channelOutput]
    exact Finset.sum_nonneg fun middle _ =>
      mul_nonneg (firstStochastic.1 input middle)
        (secondStochastic.1 middle output)
  · intro input
    rw [show (∑ output, channelOutput second (first input) output) =
        ∑ output, ∑ middle, first input middle * second middle output by
      simp only [channelOutput]]
    calc
      (∑ output, ∑ middle, first input middle * second middle output) =
          ∑ middle, ∑ output, first input middle * second middle output :=
        Finset.sum_comm
      _ = ∑ middle, first input middle * ∑ output, second middle output := by
        apply Finset.sum_congr rfl
        intro middle _
        rw [Finset.mul_sum]
      _ = ∑ middle, first input middle := by
        apply Finset.sum_congr rfl
        intro middle _
        rw [secondStochastic.2 middle, mul_one]
      _ = 1 := firstStochastic.2 input

private theorem channel_output_comp
    {Input Middle Output : Type*} [Fintype Input] [Fintype Middle]
    (first : Input → Middle → Real) (second : Middle → Output → Real)
    (mass : Input → Real) :
    channelOutput
        (fun input output => channelOutput second (first input) output) mass =
      channelOutput second (channelOutput first mass) := by
  funext output
  simp only [channelOutput]
  calc
    (∑ input, mass input * ∑ middle, first input middle * second middle output) =
        ∑ input, ∑ middle,
          (mass input * first input middle) * second middle output := by
      apply Finset.sum_congr rfl
      intro input _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro middle _
      ring
    _ = ∑ middle, ∑ input,
        (mass input * first input middle) * second middle output :=
      Finset.sum_comm
    _ = ∑ middle,
        (∑ input, mass input * first input middle) * second middle output := by
      apply Finset.sum_congr rfl
      intro middle _
      rw [Finset.sum_mul]

/-- Let `K` be an experiment, `L` a simulated experiment, `M` the simulator,
and `decision` any randomized decision rule based on `L`. If the worst-state
total-variation error between `L` and `M K` is at most `epsilon`, then the
canonical composite decision rule on `K` is stochastic and raises each
state's risk by at most `epsilon` for every loss taking values in `[0, 1]`. -/
theorem bounded_loss_risk_stability_of_simulator
    {State Observation Simulated Action : Type*}
    [Fintype State] [Nonempty State] [Fintype Observation]
    [Fintype Simulated] [Fintype Action]
    (K : State → Observation → Real)
    (L : State → Simulated → Real)
    (M : Observation → Simulated → Real)
    (decision : Simulated → Action → Real)
    (loss : State → Action → Real) (epsilon : Real)
    (KStochastic : IsRowStochastic K)
    (LStochastic : IsRowStochastic L)
    (MStochastic : IsRowStochastic M)
    (decisionStochastic : IsRowStochastic decision)
    (boundedLoss : ∀ state action,
      0 ≤ loss state action ∧ loss state action ≤ 1)
    (simulatorError :
      Finset.univ.sup' Finset.univ_nonempty
        (fun state =>
          totalVariation (L state) (channelOutput M (K state))) ≤ epsilon) :
    let transported : Observation → Action → Real :=
      fun observation action =>
        channelOutput decision (M observation) action
    IsRowStochastic transported ∧
      ∀ state,
        (∑ action,
            channelOutput transported (K state) action * loss state action) ≤
          (∑ action,
            channelOutput decision (L state) action * loss state action) +
            epsilon := by
  dsimp only
  constructor
  · exact row_stochastic_channel_comp M decision MStochastic decisionStochastic
  · intro state
    let conditionalLoss : Simulated → Real := fun simulated =>
      ∑ action, decision simulated action * loss state action
    have conditionalLossNonnegative (simulated : Simulated) :
        0 ≤ conditionalLoss simulated := by
      apply Finset.sum_nonneg
      intro action _
      exact mul_nonneg (decisionStochastic.1 simulated action)
        (boundedLoss state action).1
    have conditionalLossAtMostOne (simulated : Simulated) :
        conditionalLoss simulated ≤ 1 := by
      calc
        conditionalLoss simulated ≤
            ∑ action, decision simulated action * 1 := by
          apply Finset.sum_le_sum
          intro action _
          exact mul_le_mul_of_nonneg_left
            (boundedLoss state action).2
            (decisionStochastic.1 simulated action)
        _ = ∑ action, decision simulated action := by simp
        _ = 1 := decisionStochastic.2 simulated
    have decisionRisk (mass : Simulated → Real) :
        (∑ action,
            channelOutput decision mass action * loss state action) =
          ∑ simulated, mass simulated * conditionalLoss simulated := by
      simp only [channelOutput, conditionalLoss]
      calc
        (∑ action,
            (∑ simulated, mass simulated * decision simulated action) *
              loss state action) =
            ∑ action, ∑ simulated,
              (mass simulated * decision simulated action) *
                loss state action := by
          apply Finset.sum_congr rfl
          intro action _
          rw [Finset.sum_mul]
        _ = ∑ simulated, ∑ action,
            (mass simulated * decision simulated action) *
              loss state action := Finset.sum_comm
        _ = ∑ simulated,
            mass simulated *
              ∑ action, decision simulated action * loss state action := by
          apply Finset.sum_congr rfl
          intro simulated _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro action _
          ring
    have composedExperimentStochastic :
        IsRowStochastic
          (fun source simulated => channelOutput M (K source) simulated) :=
      row_stochastic_channel_comp K M KStochastic MStochastic
    have sameMass :
        (∑ simulated, L state simulated) =
          ∑ simulated, channelOutput M (K state) simulated :=
      (LStochastic.2 state).trans
        (composedExperimentStochastic.2 state).symm
    have stateError :
        totalVariation (L state) (channelOutput M (K state)) ≤ epsilon :=
      (Finset.le_sup'
        (fun source => totalVariation (L source) (channelOutput M (K source)))
        (Finset.mem_univ state)).trans simulatorError
    calc
      (∑ action,
          channelOutput
              (fun observation action =>
                channelOutput decision (M observation) action)
              (K state) action * loss state action) =
          ∑ simulated,
            channelOutput M (K state) simulated * conditionalLoss simulated := by
        rw [channel_output_comp M decision (K state)]
        exact decisionRisk (channelOutput M (K state))
      _ ≤ (∑ simulated, L state simulated * conditionalLoss simulated) +
          totalVariation (L state) (channelOutput M (K state)) :=
        bounded_expectation_le_add_total_variation
          (L state) (channelOutput M (K state)) conditionalLoss sameMass
          conditionalLossNonnegative conditionalLossAtMostOne
      _ ≤ (∑ simulated, L state simulated * conditionalLoss simulated) +
          epsilon := add_le_add_right stateError _
      _ = (∑ action,
            channelOutput decision (L state) action * loss state action) +
          epsilon := by rw [decisionRisk (L state)]

#print axioms bounded_loss_risk_stability_of_simulator

end D5.S3.Estimation.DecisionRisk.BoundedRiskSimulatorTransport
