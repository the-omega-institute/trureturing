/- GID: D5/S3/Estimation/DecisionRisk/PosteriorUniversalSufficiency
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/PosteriorUniversalSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal totalized finite posteriors give equal normalized one-step conditional Bayes values for every action type and real loss; zero history mass yields the zero posterior, while arbitrary-horizon experiment policies are not formalized, but posterior update dependence is proved. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'posterior_universal_sufficiency' D5 Golden/Frozen/accepted`
     returned no matches.
   * Public repository hits concern common-prior agreement, quantum future statistics,
     binary posterior thresholds, or KL/Petz equality; none identifies conditional Bayes
     values of histories with equal posteriors. The only private hit is the partition-average
     helper in `CommonPriorPosteriorAgreement`, which is neither public nor this statement.
   * Pinned Mathlib's `BayesEstimator` gives posterior integral representations and Bayes-risk
     bounds, but no equal-posterior conditional-value theorem. `smart_search.sh` and all other
     pinned Lean packages also returned no relevant declaration. The proof below uses finite
     sums, function extensionality, congruence of `Set.range` and `sInf`, and total division.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators NNReal

noncomputable section

namespace D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency

/-- The marginal mass of a history under a finite nonnegative joint weight. -/
def historyMass {Theta History : Type*} [Fintype Theta]
    (joint : Theta -> History -> NNReal) (history : History) : NNReal :=
  ∑ theta, joint theta history

/-- The totalized posterior induced by the joint weight; zero history mass gives zero. -/
def posterior {Theta History : Type*} [Fintype Theta]
    (joint : Theta -> History -> NNReal) (history : History) : Theta -> NNReal :=
  fun theta => joint theta history / historyMass joint history

/-- Expected loss computed from the joint weight and history, not from `posterior`. -/
def conditionalRisk {Theta History Action : Type*} [Fintype Theta]
    (joint : Theta -> History -> NNReal) (history : History)
    (loss : Theta -> Action -> Real) (action : Action) : Real :=
  ∑ theta, (joint theta history / historyMass joint history : NNReal) * loss theta action

/-- The normalized one-step conditional Bayes value computed on the history side. -/
def conditionalBayesValue {Theta History Action : Type*} [Fintype Theta]
    (joint : Theta -> History -> NNReal) (history : History)
    (loss : Theta -> Action -> Real) : Real :=
  sInf (Set.range (conditionalRisk joint history loss))

/-- Bayes update of a finite posterior by an experiment's observation likelihood. -/
def posteriorUpdate {Theta Observation : Type*} [Fintype Theta]
    (likelihood : Theta -> Observation -> NNReal) (prior : Theta -> NNReal)
    (observation : Observation) : Theta -> NNReal :=
  fun theta =>
    prior theta * likelihood theta observation /
      ∑ theta', prior theta' * likelihood theta' observation

/-- Equal current posteriors remain equal after every observation update. -/
theorem posterior_update_depends_only_on_posterior
    {Theta Observation : Type*} [Fintype Theta]
    (likelihood : Theta -> Observation -> NNReal) {prior prior' : Theta -> NNReal}
    (equalPrior : prior = prior') (observation : Observation) :
    posteriorUpdate likelihood prior observation =
      posteriorUpdate likelihood prior' observation := by
  exact congrArg (fun current => posteriorUpdate likelihood current observation) equalPrior

/-- Equal posteriors make every normalized history-side conditional Bayes value equal. -/
theorem posterior_universal_sufficiency
    {Theta History : Type*} [Fintype Theta]
    (joint : Theta -> History -> NNReal) {history history' : History}
    (equalPosterior : posterior joint history = posterior joint history') :
    ∀ (Action : Type) (loss : Theta -> Action -> Real),
      conditionalBayesValue joint history loss =
        conditionalBayesValue joint history' loss := by
  intro Action loss
  have equalRisk :
      conditionalRisk joint history loss = conditionalRisk joint history' loss := by
    funext action
    apply Finset.sum_congr rfl
    intro theta _
    change (posterior joint history theta : Real) * loss theta action =
      (posterior joint history' theta : Real) * loss theta action
    rw [equalPosterior]
  exact congrArg (fun risk : Action -> Real => sInf (Set.range risk)) equalRisk

/-- Histories of masses three and six with proportional state weights have the same value. -/
example (loss : Bool -> Bool -> Real) :
    let joint : Bool -> Bool -> NNReal := fun theta history =>
      if history then if theta then 4 else 2 else if theta then 2 else 1
    conditionalBayesValue joint false loss = conditionalBayesValue joint true loss := by
  dsimp only
  apply posterior_universal_sufficiency
  funext theta
  cases theta <;> norm_num [posterior, historyMass]

#print axioms posterior_universal_sufficiency

end D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency
