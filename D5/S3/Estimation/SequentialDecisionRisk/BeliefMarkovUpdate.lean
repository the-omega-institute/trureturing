/- GID: D5/S3/Estimation/SequentialDecisionRisk/BeliefMarkovUpdate
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/BeliefMarkovUpdate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Predictive marginals and Bayes updates agree, including null and empty cases. -/
/- Library-search audit trail (2026-08-30):
   * Six repository searches by object name, digest, body shape, near kin,
     generalization, and alternate vocabulary found no theorem with all three conclusions.
   * `posteriorPredictiveOutput` gives only point masses, while its main theorem assumes
     the actual-next-belief equation proved here. `inducedOutputLaw` is only generic `PMF.bind`.
   * Loogle `PMF.bind` found `PMF.bind_apply`; Loogle `?a / 0 = 0` found `div_zero`.
   * LeanSearch's semantic API returned HTTP 404. Pinned Mathlib searches found the same
     `PMF.bind_apply` and `div_zero`; no finite belief-Markov theorem was found.
-/

import D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Estimation.SequentialDecisionRisk.BeliefMarkovUpdate

open D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency

/-- The predictive output law obtained by mixing likelihoods against a current belief. -/
def predictiveOutputLaw {Theta Observation : Type*} [Fintype Theta]
    (likelihood : Theta -> Observation -> NNReal) (belief : Theta -> NNReal) :
    Observation -> NNReal :=
  fun observation =>
    Finset.univ.sum fun theta => belief theta * likelihood theta observation

/-- Marginalizing the actual hidden-state/output weight gives the predictive output law. -/
theorem output_marginal_follows_predictive_law
    {Theta Observation : Type*} [Fintype Theta]
    (likelihood : Theta -> Observation -> NNReal) (belief : Theta -> NNReal) :
    (fun observation =>
      historyMass
        (fun theta output => belief theta * likelihood theta output)
        observation) =
      predictiveOutputLaw likelihood belief := by
  rfl

#print axioms output_marginal_follows_predictive_law

/-- Conditioning the actual joint weight gives the existing canonical posterior update. -/
theorem actual_next_belief_eq_posterior_update
    {Theta Observation : Type*} [Fintype Theta]
    (likelihood : Theta -> Observation -> NNReal) (belief : Theta -> NNReal)
    (observation : Observation) :
    posterior
        (fun theta output => belief theta * likelihood theta output)
        observation =
      posteriorUpdate likelihood belief observation := by
  rfl

#print axioms actual_next_belief_eq_posterior_update

/- The source permits any version on predictive-null outputs. The repository's
`NNReal` division chooses the zero version, witnessed publicly below. -/
/-- A predictive-null output is assigned the zero posterior by the chosen totalization. -/
theorem zero_predictive_mass_update_is_zero
    {Theta Observation : Type*} [Fintype Theta]
    (likelihood : Theta -> Observation -> NNReal) (belief : Theta -> NNReal)
    (observation : Observation)
    (zeroPredictiveMass : predictiveOutputLaw likelihood belief observation = 0) :
    posteriorUpdate likelihood belief observation = fun _ => 0 := by
  unfold predictiveOutputLaw at zeroPredictiveMass
  funext theta
  simp [posteriorUpdate, zeroPredictiveMass]

#print axioms zero_predictive_mass_update_is_zero

/- Degenerate audit: an empty hidden carrier has zero predictive mass and zero update. -/
example {Observation : Type*} (likelihood : Empty -> Observation -> NNReal)
    (belief : Empty -> NNReal) (observation : Observation) :
    posteriorUpdate likelihood belief observation = fun _ => 0 := by
  apply zero_predictive_mass_update_is_zero
  simp [predictiveOutputLaw]

/- Degenerate audit: a singleton with zero likelihood also uses the zero version. -/
example {Observation : Type*} (observation : Observation) :
    posteriorUpdate (fun _ : Unit => fun _ : Observation => 0) (fun _ => 1) observation =
      fun _ => 0 := by
  apply zero_predictive_mass_update_is_zero
  simp [predictiveOutputLaw]

/- Degenerate audit: a constant-one singleton experiment leaves its belief unchanged. -/
example :
    posteriorUpdate (fun _ : Unit => fun _ : Unit => 1) (fun _ => 1) () =
      fun _ => 1 := by
  funext theta
  cases theta
  simp [posteriorUpdate]

/- Degenerate audit: the identity Boolean observation selects the observed hidden state. -/
example :
    posteriorUpdate
        (fun theta observation : Bool => if observation = theta then 1 else 0)
        (fun _ => 1) true =
      fun theta => if theta then 1 else 0 := by
  funext theta
  cases theta <;> simp [posteriorUpdate]

end D5.S3.Estimation.SequentialDecisionRisk.BeliefMarkovUpdate
