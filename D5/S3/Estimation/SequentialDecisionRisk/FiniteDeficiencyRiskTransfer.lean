/- GID: D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite experiment deficiency bounds the transfer of optimal bounded-loss risk. -/

import D5.S3.Estimation.DecisionRisk.BoundedRiskSimulatorTransport
import Mathlib.Data.ENNReal.Real

/- Library-search audit trail (2026-08-28):
   * `BoundedRiskSimulatorTransport.bounded_loss_risk_stability_of_simulator`
     is the exact fixed-simulator, fixed-decision component and is applied
     directly below; it does not itself optimize over decisions or simulators.
   * Body-shape and name searches found `bestDescentError`, but that primitive
     optimizes quotient descents whose target laws already share one codomain.
     It is not experiment deficiency between distinct observation carriers.
   * Pinned Mathlib's `ProbabilityTheory.bayesRisk_le_bayesRisk_comp` covers
     exact garbling only. No exact approximate deficiency-risk theorem was
     found. `ENNReal.le_iInf_add_iInf` supplies the two independent infima. -/

noncomputable section

open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.BoundedRiskSimulatorTransport
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

/-- The worst-state total-variation error of simulating `target` from `source`
through a specified finite Markov kernel. -/
def uniformSimulationError
    {State SourceObservation TargetObservation : Type*}
    [Fintype State] [Nonempty State]
    [Fintype SourceObservation] [Fintype TargetObservation]
    (target : State → TargetObservation → Real)
    (source : State → SourceObservation → Real)
    (simulator : FiniteMarkovKernel SourceObservation TargetObservation) : Real :=
  Finset.univ.sup' Finset.univ_nonempty fun state =>
    totalVariation (target state)
      (channelOutput simulator.1 (source state))

/-- One finite decision rule's prior-weighted expected loss. -/
def finiteBayesCost
    {State Observation Action : Type*}
    [Fintype State] [Fintype Observation] [Fintype Action]
    (prior : State → Real)
    (loss : State → Action → Real)
    (experiment : State → Observation → Real)
    (decision : Observation → Action → Real) : Real :=
  ∑ state, prior state *
    ∑ action,
      channelOutput decision (experiment state) action * loss state action

/-- Optimal finite Bayes risk, as the extended-nonnegative infimum over all
row-stochastic randomized decision rules. -/
def finiteBayesRisk
    {State Observation Action : Type*}
    [Fintype State] [Fintype Observation] [Fintype Action]
    (prior : State → Real)
    (loss : State → Action → Real)
    (experiment : State → Observation → Real) : ENNReal :=
  ⨅ decision : FiniteMarkovKernel Observation Action,
    ENNReal.ofReal (finiteBayesCost prior loss experiment decision.1)

/-- One-way finite experiment deficiency, obtained by optimizing the uniform
total-variation simulation error over all row-stochastic simulators. -/
def finiteDeficiency
    {State SourceObservation TargetObservation : Type*}
    [Fintype State] [Nonempty State]
    [Fintype SourceObservation] [Fintype TargetObservation]
    (target : State → TargetObservation → Real)
    (source : State → SourceObservation → Real) : ENNReal :=
  ⨅ simulator : FiniteMarkovKernel SourceObservation TargetObservation,
    ENNReal.ofReal (uniformSimulationError target source simulator)

private theorem uniform_simulation_error_nonnegative
    {State SourceObservation TargetObservation : Type*}
    [Fintype State] [Nonempty State]
    [Fintype SourceObservation] [Fintype TargetObservation]
    (target : State → TargetObservation → Real)
    (source : State → SourceObservation → Real)
    (simulator : FiniteMarkovKernel SourceObservation TargetObservation) :
    0 ≤ uniformSimulationError target source simulator := by
  let state : State := Classical.choice (inferInstance : Nonempty State)
  exact (total_variation_nonneg (target state)
    (channelOutput simulator.1 (source state))).trans
      (Finset.le_sup'
        (fun candidate => totalVariation (target candidate)
          (channelOutput simulator.1 (source candidate)))
        (Finset.mem_univ state))

private theorem finite_bayes_cost_nonnegative
    {State Observation Action : Type*}
    [Fintype State] [Fintype Observation] [Fintype Action]
    (prior : State → Real)
    (loss : State → Action → Real)
    (experiment : State → Observation → Real)
    (decision : Observation → Action → Real)
    (priorNonnegative : ∀ state, 0 ≤ prior state)
    (experimentStochastic : IsRowStochastic experiment)
    (decisionStochastic : IsRowStochastic decision)
    (lossNonnegative : ∀ state action, 0 ≤ loss state action) :
    0 ≤ finiteBayesCost prior loss experiment decision := by
  unfold finiteBayesCost
  apply Finset.sum_nonneg
  intro state _
  apply mul_nonneg (priorNonnegative state)
  apply Finset.sum_nonneg
  intro action _
  apply mul_nonneg _ (lossNonnegative state action)
  unfold channelOutput
  exact Finset.sum_nonneg fun observation _ =>
    mul_nonneg (experimentStochastic.1 state observation)
      (decisionStochastic.1 observation action)

private theorem finite_bayes_cost_transport
    {State SourceObservation TargetObservation Action : Type*}
    [Fintype State] [Nonempty State]
    [Fintype SourceObservation] [Fintype TargetObservation] [Fintype Action]
    (prior : State → Real)
    (loss : State → Action → Real)
    (source : State → SourceObservation → Real)
    (target : State → TargetObservation → Real)
    (simulator : FiniteMarkovKernel SourceObservation TargetObservation)
    (decision : FiniteMarkovKernel TargetObservation Action)
    (priorStochastic :
      (∀ state, 0 ≤ prior state) ∧ (∑ state, prior state) = 1)
    (sourceStochastic : IsRowStochastic source)
    (targetStochastic : IsRowStochastic target)
    (boundedLoss : ∀ state action,
      0 ≤ loss state action ∧ loss state action ≤ 1) :
    ∃ transported : FiniteMarkovKernel SourceObservation Action,
      finiteBayesCost prior loss source transported.1 ≤
        finiteBayesCost prior loss target decision.1 +
          uniformSimulationError target source simulator := by
  let error := uniformSimulationError target source simulator
  have stability := bounded_loss_risk_stability_of_simulator
    source target simulator.1 decision.1 loss error sourceStochastic
    targetStochastic simulator.2 decision.2 boundedLoss (by exact le_rfl)
  let transported : SourceObservation → Action → Real :=
    fun observation action =>
      channelOutput decision.1 (simulator.1 observation) action
  let transportedKernel : FiniteMarkovKernel SourceObservation Action :=
    ⟨transported, stability.1⟩
  refine ⟨transportedKernel, ?_⟩
  unfold finiteBayesCost
  calc
    (∑ state, prior state *
        ∑ action,
          channelOutput transportedKernel.1 (source state) action *
            loss state action) ≤
        ∑ state, prior state *
          ((∑ action,
              channelOutput decision.1 (target state) action *
                loss state action) + error) := by
      apply Finset.sum_le_sum
      intro state _
      exact mul_le_mul_of_nonneg_left (stability.2 state)
        (priorStochastic.1 state)
    _ = Finset.univ.sum (fun state =>
          prior state *
            (Finset.univ.sum (fun action =>
              channelOutput decision.1 (target state) action *
                loss state action)) + prior state * error) := by
      apply Finset.sum_congr rfl
      intro state _
      ring
    _ = (∑ state, prior state *
          ∑ action,
            channelOutput decision.1 (target state) action *
              loss state action) +
        (∑ state, prior state) * error := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = (∑ state, prior state *
          ∑ action,
            channelOutput decision.1 (target state) action *
              loss state action) + error := by
      rw [priorStochastic.2, one_mul]

/-- For a prior and a loss taking values in `[0,1]`, the optimal risk of the
source experiment is at most the optimal risk of the target experiment plus
the one-way deficiency of the target from the source. -/
theorem deficiency_risk_bound
    {State SourceObservation TargetObservation Action : Type*}
    [Fintype State] [Nonempty State]
    [Fintype SourceObservation] [Fintype TargetObservation] [Fintype Action]
    (prior : State → Real)
    (loss : State → Action → Real)
    (source : State → SourceObservation → Real)
    (target : State → TargetObservation → Real)
    (priorStochastic :
      (∀ state, 0 ≤ prior state) ∧ (∑ state, prior state) = 1)
    (sourceStochastic : IsRowStochastic source)
    (targetStochastic : IsRowStochastic target)
    (boundedLoss : ∀ state action,
      0 ≤ loss state action ∧ loss state action ≤ 1) :
    finiteBayesRisk prior loss source ≤
      finiteBayesRisk prior loss target + finiteDeficiency target source := by
  unfold finiteBayesRisk finiteDeficiency
  apply ENNReal.le_iInf_add_iInf
  intro decision simulator
  obtain ⟨transported, transportedCost⟩ := finite_bayes_cost_transport
    prior loss source target simulator decision priorStochastic
      sourceStochastic targetStochastic boundedLoss
  calc
    (⨅ candidate : FiniteMarkovKernel SourceObservation Action,
        ENNReal.ofReal
          (finiteBayesCost prior loss source candidate.1)) ≤
        ENNReal.ofReal (finiteBayesCost prior loss source transported.1) :=
      iInf_le _ transported
    _ ≤ ENNReal.ofReal
        (finiteBayesCost prior loss target decision.1 +
          uniformSimulationError target source simulator) :=
      ENNReal.ofReal_le_ofReal transportedCost
    _ = ENNReal.ofReal (finiteBayesCost prior loss target decision.1) +
        ENNReal.ofReal (uniformSimulationError target source simulator) :=
      ENNReal.ofReal_add
        (finite_bayes_cost_nonnegative prior loss target decision.1
          priorStochastic.1 targetStochastic decision.2
          (fun state action => (boundedLoss state action).1))
        (uniform_simulation_error_nonnegative target source simulator)

#print axioms deficiency_risk_bound

end D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
