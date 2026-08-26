/- GID: D5/S3/Estimation/DataProcessing/AdaptivePosteriorPolicySufficiency
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/AdaptivePosteriorPolicySufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal posteriors preserve adaptive future-output laws and recursive Bayes values. -/

import D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency
import Mathlib.Probability.ProbabilityMassFunction.Basic

/- Library-search audit trail (2026-08-26):
   * Exact family hits `posterior`, `posteriorUpdate`, and
     `posterior_update_depends_only_on_posterior` are imported from
     `PosteriorUniversalSufficiency` and reused directly.
   * Body-shape searches for a posterior mixture of experiment PMFs, a recursive
     history-extending future-output law, and a recursive policy continuation
     value found no current-tree owner.
   * Pinned Mathlib supplies the canonical `PMF` experiment kernel and complete
     lattice operations on `ENNReal`, but no adaptive posterior-sufficiency
     theorem with both future-law and continuation-value conclusions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ENNReal NNReal

noncomputable section

namespace D5.S3.Estimation.DataProcessing.AdaptivePosteriorPolicySufficiency

open D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency

universe u

/-- The predictive mass of one experiment output, constructed by mixing the
state-conditioned experiment kernel against the current posterior. -/
def posteriorPredictiveOutput
    {Theta Experiment Observation : Type*} [Fintype Theta]
    (kernel : Experiment -> Theta -> PMF Observation)
    (belief : Theta -> NNReal) (experiment : Experiment)
    (observation : Observation) : ENNReal :=
  ∑ theta, (belief theta : ENNReal) * kernel experiment theta observation

/-- The finite-horizon future-output law generated recursively from the current
history. A policy may adapt to the remaining horizon and the current posterior;
after each output, the supplied history extension is used before the next step. -/
def adaptiveFutureOutputLaw
    {Theta History Experiment Observation : Type*} [Fintype Theta]
    (joint : Theta -> History -> NNReal)
    (extend : History -> Experiment -> Observation -> History)
    (kernel : Experiment -> Theta -> PMF Observation)
    (policy : Nat -> (Theta -> NNReal) -> Experiment) :
    Nat -> History -> List Observation -> ENNReal
  | 0, _history, transcript => if transcript = [] then 1 else 0
  | horizon + 1, history, transcript =>
      match transcript with
      | [] => 0
      | observation :: rest =>
          let belief := posterior joint history
          let experiment := policy horizon belief
          posteriorPredictiveOutput kernel belief experiment observation *
            adaptiveFutureOutputLaw joint extend kernel policy horizon
              (extend history experiment observation) rest

/-- A recursively adaptive conditional Bayes value. At horizon zero the agent
chooses an action minimizing posterior expected loss. At a positive horizon it
follows the experiment policy and averages the continuation value over the
posterior predictive output law. -/
def adaptiveContinuationValue
    {Theta History Experiment Observation : Type*} [Fintype Theta]
    (joint : Theta -> History -> NNReal)
    (extend : History -> Experiment -> Observation -> History)
    (kernel : Experiment -> Theta -> PMF Observation)
    (policy : Nat -> (Theta -> NNReal) -> Experiment)
    {Action : Type u} (loss : Theta -> Action -> ENNReal) :
    Nat -> History -> ENNReal
  | 0, history =>
      ⨅ action, ∑ theta,
        (posterior joint history theta : ENNReal) * loss theta action
  | horizon + 1, history =>
      let belief := posterior joint history
      let experiment := policy horizon belief
      ∑' observation,
        posteriorPredictiveOutput kernel belief experiment observation *
          adaptiveContinuationValue joint extend kernel policy loss horizon
            (extend history experiment observation)

/-- If extending a history realizes the canonical Bayes update, then equal
current posteriors give equal complete future-output laws and equal recursive
conditional Bayes values for every belief-adaptive finite-horizon experiment
policy, action carrier, and nonnegative loss. -/
theorem posterior_adaptive_policy_universal_sufficiency
    {Theta History Experiment Observation : Type*} [Fintype Theta]
    (joint : Theta -> History -> NNReal)
    (extend : History -> Experiment -> Observation -> History)
    (kernel : Experiment -> Theta -> PMF Observation)
    (bayesConditioned : forall history experiment observation,
      posterior joint (extend history experiment observation) =
        posteriorUpdate
          (fun theta output => (kernel experiment theta output).toNNReal)
          (posterior joint history) observation)
    {history history' : History}
    (equalPosterior : posterior joint history = posterior joint history') :
    forall (policy : Nat -> (Theta -> NNReal) -> Experiment)
      (Action : Type u) (loss : Theta -> Action -> ENNReal) (horizon : Nat),
      adaptiveFutureOutputLaw joint extend kernel policy horizon history =
          adaptiveFutureOutputLaw joint extend kernel policy horizon history' /\
        adaptiveContinuationValue joint extend kernel policy loss horizon history =
          adaptiveContinuationValue joint extend kernel policy loss horizon history' := by
  intro policy Action loss horizon
  induction horizon generalizing history history' with
  | zero =>
      constructor
      · rfl
      · simp only [adaptiveContinuationValue]
        apply iInf_congr
        intro action
        apply Finset.sum_congr rfl
        intro theta _
        rw [equalPosterior]
  | succ horizon inductionHypothesis =>
      let belief := posterior joint history
      let belief' := posterior joint history'
      let experiment := policy horizon belief
      have sameBelief : belief = belief' := equalPosterior
      have sameExperiment : experiment = policy horizon belief' :=
        congrArg (policy horizon) sameBelief
      have predictiveEqual (observation : Observation) :
          posteriorPredictiveOutput kernel belief experiment observation =
            posteriorPredictiveOutput kernel belief' experiment observation := by
        apply Finset.sum_congr rfl
        intro theta _
        rw [sameBelief]
      have nextPosterior (observation : Observation) :
          posterior joint (extend history experiment observation) =
            posterior joint (extend history' experiment observation) := by
        rw [bayesConditioned, bayesConditioned]
        exact posterior_update_depends_only_on_posterior
          (fun theta output => (kernel experiment theta output).toNNReal)
          sameBelief observation
      constructor
      · funext transcript
        cases transcript with
        | nil =>
            simp [adaptiveFutureOutputLaw]
        | cons observation rest =>
            simp only [adaptiveFutureOutputLaw]
            rw [← sameExperiment, predictiveEqual observation]
            exact congrArg
              (fun continuation =>
                posteriorPredictiveOutput kernel belief' experiment observation *
                  continuation)
              (congrFun
                (inductionHypothesis
                  (history := extend history experiment observation)
                  (history' := extend history' experiment observation)
                  (nextPosterior observation)).1
                rest)
      · simp only [adaptiveContinuationValue]
        rw [← sameExperiment]
        apply tsum_congr
        intro observation
        rw [predictiveEqual observation]
        exact congrArg
          (fun continuation =>
            posteriorPredictiveOutput kernel belief' experiment observation *
              continuation)
          (inductionHypothesis
            (history := extend history experiment observation)
            (history' := extend history' experiment observation)
            (nextPosterior observation)).2

#print axioms posterior_adaptive_policy_universal_sufficiency

end D5.S3.Estimation.DataProcessing.AdaptivePosteriorPolicySufficiency
