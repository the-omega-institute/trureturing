/- GID: D5/S3/ConceptDynamics/ExperimentDesign/ThreeStateAdaptiveEarlyStopping
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentDesign/ThreeStateAdaptiveEarlyStopping
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A three-state early-stopping tree keeps exactness and lowers mean cost. -/

import D5.S3.ConceptDynamics.Experiment.PosteriorInformationGainIncrease
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-26):
   * `PosteriorInformationGainIncrease` supplies the established three-state
     `Option Bool` carrier shape and the source readouts `Option.isNone` and
     the `some true` indicator, but exposes them only as theorem-local lets.
   * Searches for a static transcript, early-stopping transcript, call count,
     expected call cost, and the complete three-clause result found no D5 hit.
     All source objects are therefore constructed as public theorem lets; no
     top-level `def` or `abbrev` is introduced.
   * Pinned Mathlib provides `Fintype.sum_option`, `Fintype.sum_bool`, and real
     normalization, but no adaptive experiment-cost theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.ConceptDynamics.ExperimentDesign.ThreeStateAdaptiveEarlyStopping

/-- For the source's three-state prior and two deterministic experiments, both
the fixed two-test transcript and the early-stopping transcript identify the
state exactly. The adaptive tree has worst-case length two, but its expected
length is `1 + 2 * epsilon`, strictly below the static length two. -/
theorem three_state_adaptive_early_stopping_strict_advantage
    (epsilon : Real) (epsilonPositive : 0 < epsilon)
    (epsilonUpper : epsilon < 1 / 2) :
    let State := Option Bool
    let priorMass : State -> Real := fun state =>
      match state with
      | none => 1 - 2 * epsilon
      | some _ => epsilon
    let firstReadout : State -> Bool := Option.isNone
    let secondReadout : State -> Bool := fun state =>
      match state with
      | some true => true
      | _ => false
    let staticTranscript : State -> List Bool := fun state =>
      [firstReadout state, secondReadout state]
    let adaptiveTranscript : State -> List Bool := fun state =>
      if firstReadout state then [true] else [false, secondReadout state]
    ((∀ state : State, 0 ≤ priorMass state) ∧
        ∑ state : State, priorMass state = 1) ∧
      Function.Injective staticTranscript ∧
      Function.Injective adaptiveTranscript ∧
      ((∀ state : State, (adaptiveTranscript state).length ≤ 2) ∧
        ∃ state : State, (adaptiveTranscript state).length = 2) ∧
      (∑ state : State,
        priorMass state * (staticTranscript state).length = 2) ∧
      (∑ state : State,
        priorMass state * (adaptiveTranscript state).length =
          1 + 2 * epsilon) ∧
      (∑ state : State,
        priorMass state * (adaptiveTranscript state).length) <
        ∑ state : State,
          priorMass state * (staticTranscript state).length := by
  dsimp only
  constructor
  · constructor
    · intro state
      cases state with
      | none => dsimp; linarith
      | some value => exact epsilonPositive.le
    · simp [Fintype.sum_option]
  constructor
  · decide
  constructor
  · decide
  constructor
  · constructor
    · decide
    · exact ⟨some false, rfl⟩
  constructor
  · norm_num [Fintype.sum_option, Fintype.sum_bool]
    ring
  constructor
  · simp [Fintype.sum_option]
    ring
  · simp [Fintype.sum_option]
    linarith

#print axioms three_state_adaptive_early_stopping_strict_advantage

end D5.S3.ConceptDynamics.ExperimentDesign.ThreeStateAdaptiveEarlyStopping
