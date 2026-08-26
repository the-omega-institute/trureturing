/- GID: D5/S3/ConceptDynamics/Experiment/PosteriorInformationGainIncrease
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/PosteriorInformationGainIncrease
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Actual-posterior information gain can increase for deterministic experiments. -/

import D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/- Library-search audit trail (2026-08-25):
   * Repository searches for adaptive diminishing returns, actual-posterior
     entropy utility, and deterministic conditional independence found no
     exact theorem or countermodel.
   * Exact family hits `readoutTargetLaw`, `pushforward`, `marginal`, and
     `mutualInformation` supply the finite joint-law, posterior-normalization,
     marginal, and information primitives used below; none is redeclared.
   * `TargetPairCoverageInformationContrast` is a nearby concrete information
     countermodel, but it has no posterior update or adaptive comparison.
   * Pinned Mathlib has no finite mutual-information countermodel. Its exact
     scalar hit `Real.binEntropy_lt_log_two` proves the strict entropy gap and
     is applied directly after evaluating the two finite laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Experiment.PosteriorInformationGainIncrease

open D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.Divergence.ChainRule
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MutualInformation

open scoped BigOperators

/-- Three hidden states with deterministic readouts give a concrete violation
of adaptive diminishing returns. The first readout isolates the high-mass
state. On the realized complementary branch, Bayes restriction makes the
other two states uniform, increasing the information supplied by the same
second readout from binary entropy at one quarter to `log 2`. The displayed
conditional output law factors into its marginals at every hidden state. -/
theorem actual_posterior_information_gain_can_increase :
    let priorMass : Option Bool -> Real := fun state =>
      match state with
      | none => 1 / 2
      | some _ => 1 / 4
    let firstReadout : Option Bool -> Bool := Option.isNone
    let secondReadout : Option Bool -> Bool := fun state =>
      match state with
      | some true => true
      | _ => false
    let posteriorMass : Option Bool -> Real := fun state =>
      if firstReadout state = false then
        priorMass state / pushforward firstReadout priorMass false
      else 0
    let conditionalOutputLaw : Option Bool -> Bool × Bool -> Real :=
      fun state output =>
        if output = (firstReadout state, secondReadout state) then 1 else 0
    ((forall state, 0 <= priorMass state) /\ ∑ state, priorMass state = 1) /\
      0 < pushforward firstReadout priorMass false /\
      ((forall state, 0 <= posteriorMass state) /\ ∑ state, posteriorMass state = 1) /\
      (forall state output,
        conditionalOutputLaw state output =
          marginal (conditionalOutputLaw state) output.1 *
            marginal
              (fun swapped : Bool × Bool =>
                conditionalOutputLaw state (swapped.2, swapped.1)) output.2) /\
      mutualInformation (readoutTargetLaw priorMass secondReadout id) <
        mutualInformation (readoutTargetLaw posteriorMass secondReadout id) := by
  dsimp only
  constructor
  · constructor
    · intro state
      cases state <;> norm_num
    · norm_num [Fintype.sum_option, Fintype.sum_bool]
  constructor
  · norm_num [pushforward, Fintype.sum_option, Fintype.sum_bool]
  constructor
  · constructor
    · intro state
      cases state with
      | none => norm_num [pushforward, Fintype.sum_option, Fintype.sum_bool]
      | some value =>
          cases value <;>
            norm_num [pushforward, Fintype.sum_option, Fintype.sum_bool]
    · norm_num [pushforward, Fintype.sum_option, Fintype.sum_bool]
  constructor
  · intro state output
    rcases output with ⟨firstValue, secondValue⟩
    cases state with
    | none =>
        cases firstValue <;> cases secondValue <;>
          norm_num [marginal, Fintype.sum_bool]
    | some value =>
        cases value <;> cases firstValue <;> cases secondValue <;>
          norm_num [marginal, Fintype.sum_bool]
  · have priorInformation :
        mutualInformation
            (readoutTargetLaw
              (fun state : Option Bool =>
                match state with
                | none => 1 / 2
                | some _ => 1 / 4)
              (fun state : Option Bool =>
                match state with
                | some true => true
                | _ => false)
              id) =
          Real.binEntropy (1 / 4) := by
      norm_num [mutualInformation, klDivergence, marginal, readoutTargetLaw,
        pushforward, Fintype.sum_option, Fintype.sum_bool,
        Fintype.sum_prod_type, Real.binEntropy]
      simp
      ring
    have posteriorInformation :
        mutualInformation
            (readoutTargetLaw
              (fun state : Option Bool =>
                if Option.isNone state = false then
                  (match state with
                    | none => 1 / 2
                    | some _ => 1 / 4) /
                      pushforward Option.isNone
                        (fun state : Option Bool =>
                          match state with
                          | none => 1 / 2
                          | some _ => 1 / 4) false
                else 0)
              (fun state : Option Bool =>
                match state with
                | some true => true
                | _ => false)
              id) =
          Real.log 2 := by
      norm_num [mutualInformation, klDivergence, marginal, readoutTargetLaw,
        pushforward, Fintype.sum_option, Fintype.sum_bool,
        Fintype.sum_prod_type]
      simp
      ring
    rw [priorInformation, posteriorInformation]
    exact Real.binEntropy_lt_log_two.mpr (by norm_num)

#print axioms actual_posterior_information_gain_can_increase

end D5.S3.ConceptDynamics.Experiment.PosteriorInformationGainIncrease
