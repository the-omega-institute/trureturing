/- GID: D5/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation
   generality: G
   mirror-B: D5/B/S3/Estimation/ExperimentCost/StaticAdaptiveSubmodularitySeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rare posterior activation preserves expected but breaks pathwise returns. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-25):
   * `Finset.sum` hits supplied the finite expectation used below. Searches for
     `ProbabilityTheory` and `PMF` found measure-valued infrastructure, but no exact
     static-versus-adaptive counterexample; rational finite masses avoid unused measure theory.
   * `Finset.inf`/`Finset.sup` searches found finite extrema tools, but this three-state
     decision-value witness requires only exact finite sums and rational normalization.
   * `DependencyClosureAdmissionAntitone` concerns evidence-role contamination;
     `WeightedResidualCoverage` proves deterministic coverage submodularity;
     `WaitingCostValueReversal` concerns positive delay cost; and `DirectlyProvableLaws`
     concerns definition capture. None has posterior transcripts or both properties below.
   * `PosteriorInformationGainIncrease` proves one realized entropy-gain increase, but has
     no named static/adaptive property and no expected-gain inequality. The present witness
     instead uses a genuinely rare branch of mass `1 / 10` and proves both sides explicitly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.ExperimentCost.StaticAdaptiveSubmodularitySeparation

open scoped BigOperators

/-- A finite rational mass function is normalized and pointwise nonnegative. -/
def ProbabilityMass {Outcome : Type*} [Fintype Outcome]
    (mass : Outcome -> ℚ) : Prop :=
  (forall outcome, 0 <= mass outcome) /\ ∑ outcome, mass outcome = 1

/-- Two-stage static submodularity: after one fixed experiment, every available
next experiment has no larger marginal gain on average over the first output. -/
def StaticSubmodular {Outcome Experiment : Type*} [Fintype Outcome]
    (outcomeMass : Outcome -> ℚ) (available : Experiment -> Prop)
    (priorGain : Experiment -> ℚ) (pathGain : Outcome -> Experiment -> ℚ) : Prop :=
  ProbabilityMass outcomeMass /\
    forall experiment, available experiment ->
      (∑ outcome, outcomeMass outcome * pathGain outcome experiment) <=
        priorGain experiment

/-- Two-stage adaptive submodularity: on every positive-probability realized
output, every still-available experiment has no larger marginal gain. -/
def AdaptiveSubmodular {Outcome Experiment : Type*} [Fintype Outcome]
    (outcomeMass : Outcome -> ℚ) (available : Experiment -> Prop)
    (priorGain : Experiment -> ℚ) (pathGain : Outcome -> Experiment -> ℚ) : Prop :=
  ProbabilityMass outcomeMass /\
    forall experiment outcome, available experiment -> 0 < outcomeMass outcome ->
      pathGain outcome experiment <= priorGain experiment

/-- Pointwise adaptive diminishing returns implies its prior expectation in
the finite two-stage specialization. Zero-mass outputs contribute zero. -/
theorem adaptive_submodular_implies_static_submodular
    {Outcome Experiment : Type*} [Fintype Outcome]
    (outcomeMass : Outcome -> ℚ) (available : Experiment -> Prop)
    (priorGain : Experiment -> ℚ) (pathGain : Outcome -> Experiment -> ℚ)
    (adaptive : AdaptiveSubmodular outcomeMass available priorGain pathGain) :
    StaticSubmodular outcomeMass available priorGain pathGain := by
  rcases adaptive with ⟨massLaw, pathwise⟩
  refine ⟨massLaw, ?_⟩
  intro experiment isAvailable
  calc
    (∑ outcome, outcomeMass outcome * pathGain outcome experiment) <=
        ∑ outcome, outcomeMass outcome * priorGain experiment := by
      apply Finset.sum_le_sum
      intro outcome _
      by_cases zeroMass : outcomeMass outcome = 0
      · simp [zeroMass]
      · have positiveMass : 0 < outcomeMass outcome :=
          lt_of_le_of_ne (massLaw.1 outcome) (Ne.symm zeroMass)
        exact mul_le_mul_of_nonneg_left
          (pathwise experiment outcome isAvailable positiveMass) (massLaw.1 outcome)
    _ = (∑ outcome, outcomeMass outcome) * priorGain experiment := by
      rw [Finset.sum_mul]
    _ = priorGain experiment := by rw [massLaw.2, one_mul]

#print axioms adaptive_submodular_implies_static_submodular

/-- Three hidden states: `none` is common and the two Boolean values are rare. -/
abbrev RareState := Option Bool

/-- Two experiments, represented by the finite Boolean type. -/
abbrev RareExperiment := Bool

/-- The first experiment gates the common state from the two rare states. -/
def gateExperiment : RareExperiment := false

/-- The second experiment detects the `some true` rare state. -/
def specialistExperiment : RareExperiment := true

/-- A common state has mass `9 / 10`; each rare state has mass `1 / 20`. -/
def rarePriorMass : RareState -> ℚ
  | none => 9 / 10
  | some _ => 1 / 20

/-- Both experiments are deterministic Boolean readouts. -/
def rareReadout : RareExperiment -> RareState -> Bool
  | false, none => true
  | false, some _ => false
  | true, some true => true
  | true, _ => false

/-- The prior probability of a realized output of a deterministic experiment. -/
def readoutOutcomeMass (experiment : RareExperiment) (outcome : Bool) : ℚ :=
  ∑ state, if rareReadout experiment state = outcome then rarePriorMass state else 0

/-- Bayes restriction to one positive-probability deterministic output fiber. -/
def posteriorAfterReadout
    (experiment : RareExperiment) (outcome : Bool) (state : RareState) : ℚ :=
  if rareReadout experiment state = outcome then
    rarePriorMass state / readoutOutcomeMass experiment outcome
  else 0

/-- The output law of the first, gating experiment. -/
def rareGateOutcomeMass : Bool -> ℚ := readoutOutcomeMass gateExperiment

/-- After the gate is observed, only the specialist remains available. -/
def availableAfterGate : RareExperiment -> Prop
  | false => False
  | true => True

/-- The specialist's prior marginal decision value is the right-state mass. -/
def rarePriorMarginalGain : RareExperiment -> ℚ
  | false => 0
  | true => rarePriorMass (some true)

/-- On a realized gate output, the specialist's posterior marginal decision
value is the posterior right-state mass. -/
def rarePathMarginalGain (outcome : Bool) : RareExperiment -> ℚ
  | false => 0
  | true => posteriorAfterReadout gateExperiment outcome (some true)

/-- The prior and gate-output masses are probability laws, and the gate's
`false` output is the rare branch of probability `1 / 10`. -/
theorem rare_prior_and_gate_are_normalized :
    ProbabilityMass rarePriorMass /\
      ProbabilityMass rareGateOutcomeMass /\ rareGateOutcomeMass false = 1 / 10 := by
  constructor
  · constructor
    · intro state
      cases state with
      | none => norm_num [rarePriorMass]
      | some value => cases value <;> norm_num [rarePriorMass]
    · norm_num [rarePriorMass, Fintype.sum_option, Fintype.sum_bool]
  constructor
  · constructor
    · intro outcome
      cases outcome <;>
        norm_num [rareGateOutcomeMass, readoutOutcomeMass, gateExperiment,
          rareReadout, rarePriorMass, Fintype.sum_option, Fintype.sum_bool]
    · norm_num [rareGateOutcomeMass, readoutOutcomeMass, gateExperiment,
        rareReadout, rarePriorMass, Fintype.sum_option, Fintype.sum_bool]
  · norm_num [rareGateOutcomeMass, readoutOutcomeMass, gateExperiment,
      rareReadout, rarePriorMass, Fintype.sum_option, Fintype.sum_bool]

#print axioms rare_prior_and_gate_are_normalized

/-- The rare gate output removes the common state and makes the two rare states
equiprobable, raising the specialist's marginal gain from `1 / 20` to `1 / 2`. -/
theorem rare_output_posterior_activates_specialist :
    posteriorAfterReadout gateExperiment false none = 0 /\
      posteriorAfterReadout gateExperiment false (some false) = 1 / 2 /\
      posteriorAfterReadout gateExperiment false (some true) = 1 / 2 /\
      rarePriorMarginalGain specialistExperiment = 1 / 20 /\
      rarePathMarginalGain false specialistExperiment = 1 / 2 := by
  norm_num [posteriorAfterReadout, readoutOutcomeMass, gateExperiment,
    specialistExperiment, rareReadout, rarePriorMass, rarePriorMarginalGain,
    rarePathMarginalGain, Fintype.sum_option, Fintype.sum_bool]

#print axioms rare_output_posterior_activates_specialist

/-- Averaging over both gate outputs preserves the specialist's prior marginal
gain, so the concrete instance satisfies static expected diminishing returns. -/
theorem rare_branch_static_submodular :
    StaticSubmodular rareGateOutcomeMass availableAfterGate
      rarePriorMarginalGain rarePathMarginalGain := by
  refine ⟨rare_prior_and_gate_are_normalized.2.1, ?_⟩
  intro experiment isAvailable
  cases experiment with
  | false => exact False.elim isAvailable
  | true =>
    norm_num [rareGateOutcomeMass, rarePriorMarginalGain,
      rarePathMarginalGain, posteriorAfterReadout, readoutOutcomeMass,
      gateExperiment, rareReadout, rarePriorMass, Fintype.sum_option,
      Fintype.sum_bool]

#print axioms rare_branch_static_submodular

/-- The positive-probability rare output raises the specialist's realized
marginal gain, so pathwise adaptive diminishing returns fails. -/
theorem rare_branch_not_adaptive_submodular :
    ¬AdaptiveSubmodular rareGateOutcomeMass availableAfterGate
      rarePriorMarginalGain rarePathMarginalGain := by
  intro adaptive
  have pathBound := adaptive.2 specialistExperiment false (by trivial)
    (by
      rw [rare_prior_and_gate_are_normalized.2.2]
      norm_num)
  norm_num [specialistExperiment, rarePriorMarginalGain, rarePathMarginalGain,
    posteriorAfterReadout, readoutOutcomeMass, gateExperiment, rareReadout,
    rarePriorMass, Fintype.sum_option, Fintype.sum_bool] at pathBound

#print axioms rare_branch_not_adaptive_submodular

/-- FPOD principle 246.1: static expected diminishing returns does not imply
pathwise adaptive diminishing returns, witnessed by the rare posterior branch. -/
theorem fpod_principle_246_1 :
    ¬(StaticSubmodular rareGateOutcomeMass availableAfterGate
          rarePriorMarginalGain rarePathMarginalGain ->
        AdaptiveSubmodular rareGateOutcomeMass availableAfterGate
          rarePriorMarginalGain rarePathMarginalGain) := by
  intro implication
  exact rare_branch_not_adaptive_submodular (implication rare_branch_static_submodular)

#print axioms fpod_principle_246_1

/-- With no experiments, both properties are vacuous once the output mass is normalized. -/
theorem empty_experiment_family_satisfies_both :
    StaticSubmodular rareGateOutcomeMass (fun _ : Empty => False)
        Empty.elim (fun _ => Empty.elim) /\
      AdaptiveSubmodular rareGateOutcomeMass (fun _ : Empty => False)
        Empty.elim (fun _ => Empty.elim) := by
  have adaptive :
      AdaptiveSubmodular rareGateOutcomeMass (fun _ : Empty => False)
        Empty.elim (fun _ => Empty.elim) := by
    refine ⟨rare_prior_and_gate_are_normalized.2.1, ?_⟩
    intro experiment
    exact Empty.elim experiment
  exact ⟨adaptive_submodular_implies_static_submodular _ _ _ _ adaptive, adaptive⟩

#print axioms empty_experiment_family_satisfies_both

/-- A singleton family with its sole experiment already observed has no
available next experiment, so both properties are vacuous. -/
theorem singleton_experiment_family_satisfies_both :
    StaticSubmodular rareGateOutcomeMass (fun _ : Unit => False)
        (fun _ => 0) (fun _ _ => 0) /\
      AdaptiveSubmodular rareGateOutcomeMass (fun _ : Unit => False)
        (fun _ => 0) (fun _ _ => 0) := by
  have adaptive :
      AdaptiveSubmodular rareGateOutcomeMass (fun _ : Unit => False)
        (fun _ => 0) (fun _ _ => 0) := by
    refine ⟨rare_prior_and_gate_are_normalized.2.1, ?_⟩
    intro _ _ isAvailable
    exact False.elim isAvailable
  exact ⟨adaptive_submodular_implies_static_submodular _ _ _ _ adaptive, adaptive⟩

#print axioms singleton_experiment_family_satisfies_both

/-- Constant zero marginal gain satisfies both expected and pathwise diminishing returns. -/
theorem constant_gain_satisfies_both :
    StaticSubmodular rareGateOutcomeMass (fun _ : Bool => True)
        (fun _ => 0) (fun _ _ => 0) /\
      AdaptiveSubmodular rareGateOutcomeMass (fun _ : Bool => True)
        (fun _ => 0) (fun _ _ => 0) := by
  have adaptive :
      AdaptiveSubmodular rareGateOutcomeMass (fun _ : Bool => True)
        (fun _ => 0) (fun _ _ => 0) := by
    refine ⟨rare_prior_and_gate_are_normalized.2.1, ?_⟩
    intro _ _ _ _
    rfl
  exact ⟨adaptive_submodular_implies_static_submodular _ _ _ _ adaptive, adaptive⟩

#print axioms constant_gain_satisfies_both

/-- If the posterior never changes any marginal gain, adaptive and static
diminishing returns both reduce to equality. -/
theorem posterior_not_updating_satisfies_both :
    StaticSubmodular rareGateOutcomeMass availableAfterGate
        rarePriorMarginalGain (fun _ => rarePriorMarginalGain) /\
      AdaptiveSubmodular rareGateOutcomeMass availableAfterGate
        rarePriorMarginalGain (fun _ => rarePriorMarginalGain) := by
  have adaptive :
      AdaptiveSubmodular rareGateOutcomeMass availableAfterGate
        rarePriorMarginalGain (fun _ => rarePriorMarginalGain) := by
    refine ⟨rare_prior_and_gate_are_normalized.2.1, ?_⟩
    intro _ _ _ _
    rfl
  exact ⟨adaptive_submodular_implies_static_submodular _ _ _ _ adaptive, adaptive⟩

#print axioms posterior_not_updating_satisfies_both

end D5.S3.Estimation.ExperimentCost.StaticAdaptiveSubmodularitySeparation
