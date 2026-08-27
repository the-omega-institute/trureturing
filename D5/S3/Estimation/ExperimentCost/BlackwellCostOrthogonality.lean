/- GID: D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality
   generality: G
   mirror-B: D5/B/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Blackwell order permits either cost direction; equal or constant costs do not. -/

/- Library-search audit trail (2026-08-27):
   * All thirteen `Estimation/DecisionRisk` modules were checked. The exact Blackwell
     definition, map theorem, and Bayes-risk theorem occur only in
     `GarblingIncreasesBayesRisk`; they are imported and applied directly.
   * `ExperimentStatePosteriorDecisionSeparation` separates a law quotient from posterior
     decisions. It does not compare Blackwell dominance with an external cost assignment.
   * `FixedSuiteBayesRiskFloor`, `BoundedRiskSimulatorTransport`, and `DescentDefectBounds`
     concern risk floors or simulation error, not arbitrary experiment costs.
   * `CausalPosteriorSufficiency`, `PosteriorFuturePolicySufficiency`, and
     `PosteriorHistoryCompression` concern posterior-determined predictions and values.
   * `LawRepresentationCanonicalQuotient`, the two stochastic-descent modules, the stopping
     bound, and universal posterior sufficiency have no external cost order.
   * `RefinementRiskCostTradeoff` uses a particular attained-coordinate cardinality and proves
     its monotonicity. It is not the axiom-free external assignment formalized here.
   * Pinned Mathlib provides `Kernel.id_map`, `Kernel.deterministic_map`, and
     `MeasureTheory.injective_dirac` for the concrete nontrivial Boolean witnesses.
-/

import D5.S3.Estimation.DecisionRisk.GarblingIncreasesBayesRisk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.ExperimentCost.BlackwellCostOrthogonality

open MeasureTheory ProbabilityTheory
open D5.S3.Estimation.DecisionRisk.GarblingIncreasesBayesRisk

/-- A nonnegative implementation cost assigned externally to each experiment kernel.
No compatibility with the Blackwell order is part of this definition. -/
def ExperimentCost {Theta X : Type*}
    [MeasurableSpace Theta] [MeasurableSpace X] :=
  Kernel Theta X -> NNReal

private noncomputable def identityExperiment : Kernel Bool Bool :=
  Kernel.id

private noncomputable def erasedExperiment : Kernel Bool Bool :=
  Kernel.deterministic (fun _ => false) measurable_const

private theorem identity_experiment_ne_erased_experiment :
    identityExperiment ≠ erasedExperiment := by
  intro equalExperiments
  have equalAtTrue := congrArg (fun K : Kernel Bool Bool => K true) equalExperiments
  have equalDirac : Measure.dirac true = Measure.dirac false := by
    simpa [identityExperiment, erasedExperiment, Kernel.id_apply,
      Kernel.deterministic_apply] using equalAtTrue
  exact (by decide : true ≠ false) (injective_dirac equalDirac)

private theorem identity_experiment_dominates_erased_experiment :
    BlackwellDominates identityExperiment erasedExperiment := by
  have dominance := blackwellDominates_map
    (Kernel.id : Kernel Bool Bool) (fun _ : Bool => false) measurable_const
  rw [Kernel.id_map measurable_const] at dominance
  simpa [identityExperiment, erasedExperiment] using dominance

/-- A strictly more informative experiment can have strictly higher external cost.
The Boolean identity and erasure kernels are distinct, so this is not reflexivity. -/
theorem exists_blackwell_dominance_with_higher_cost :
    exists (P Q : Kernel Bool Bool) (cost : ExperimentCost (Theta := Bool) (X := Bool)),
      P ≠ Q /\ BlackwellDominates P Q /\ cost P > cost Q := by
  classical
  let cost : ExperimentCost (Theta := Bool) (X := Bool) := fun experiment =>
    if experiment = erasedExperiment then 0 else 1
  refine ⟨identityExperiment, erasedExperiment, cost,
    identity_experiment_ne_erased_experiment,
    identity_experiment_dominates_erased_experiment, ?_⟩
  simp [cost, identity_experiment_ne_erased_experiment]
#print axioms exists_blackwell_dominance_with_higher_cost

/-- A strictly more informative experiment can also have strictly lower external cost,
using the same distinct Boolean experiment pair and the opposite cost assignment. -/
theorem exists_blackwell_dominance_with_lower_cost :
    exists (P Q : Kernel Bool Bool) (cost : ExperimentCost (Theta := Bool) (X := Bool)),
      P ≠ Q /\ BlackwellDominates P Q /\ cost P < cost Q := by
  classical
  let cost : ExperimentCost (Theta := Bool) (X := Bool) := fun experiment =>
    if experiment = erasedExperiment then 1 else 0
  refine ⟨identityExperiment, erasedExperiment, cost,
    identity_experiment_ne_erased_experiment,
    identity_experiment_dominates_erased_experiment, ?_⟩
  simp [cost, identity_experiment_ne_erased_experiment]
#print axioms exists_blackwell_dominance_with_lower_cost

/-- Equal experiment kernels necessarily receive equal values from every cost function. -/
theorem equal_experiments_have_equal_cost
    {Theta X : Type*} [MeasurableSpace Theta] [MeasurableSpace X]
    (cost : ExperimentCost (Theta := Theta) (X := X))
    {P Q : Kernel Theta X} (equalExperiments : P = Q) :
    cost P = cost Q :=
  congrArg cost equalExperiments
#print axioms equal_experiments_have_equal_cost

/-- A constant cost assignment cannot witness either strict cost direction. -/
theorem constant_experiment_cost_cannot_strictly_compare
    {Theta X : Type*} [MeasurableSpace Theta] [MeasurableSpace X]
    (value : NNReal) (P Q : Kernel Theta X) :
    not ((fun _ : Kernel Theta X => value) P > (fun _ : Kernel Theta X => value) Q) /\
      not ((fun _ : Kernel Theta X => value) P < (fun _ : Kernel Theta X => value) Q) := by
  simp
#print axioms constant_experiment_cost_cannot_strictly_compare

/-- Constant Boolean experiments are Blackwell-equivalent: either can be obtained by
constant postprocessing of the other. -/
theorem constant_boolean_experiments_are_blackwell_equivalent :
    BlackwellDominates
        (Kernel.deterministic (fun _ : Bool => false) measurable_const)
        (Kernel.deterministic (fun _ : Bool => true) measurable_const) /\
      BlackwellDominates
        (Kernel.deterministic (fun _ : Bool => true) measurable_const)
        (Kernel.deterministic (fun _ : Bool => false) measurable_const) := by
  constructor
  · have dominance := blackwellDominates_map
      (Kernel.deterministic (fun _ : Bool => false) measurable_const)
      (fun _ : Bool => true) measurable_const
    simpa [Kernel.deterministic_map, Function.comp_def] using dominance
  · have dominance := blackwellDominates_map
      (Kernel.deterministic (fun _ : Bool => true) measurable_const)
      (fun _ : Bool => false) measurable_const
    simpa [Kernel.deterministic_map, Function.comp_def] using dominance
#print axioms constant_boolean_experiments_are_blackwell_equivalent

/-- Blackwell dominance still compares decision information through optimal Bayes risk. -/
theorem blackwell_dominance_still_compares_bayes_risk
    {Theta X X' Y : Type*}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
    (P : Kernel Theta X) (Q : Kernel Theta X') (dominance : BlackwellDominates P Q) :
    forall (loss : Theta -> Y -> ENNReal) (prior : Measure Theta),
      bayesRisk loss P prior <= bayesRisk loss Q prior :=
  bayesRisk_le_of_blackwellDominates P Q dominance
#print axioms blackwell_dominance_still_compares_bayes_risk

/-- Empty experiment carriers introduce no counterexample to equality transport. -/
example (cost : ExperimentCost (Theta := Empty) (X := Empty))
    (P Q : Kernel Empty Empty) (equalExperiments : P = Q) :
    cost P = cost Q :=
  equal_experiments_have_equal_cost cost equalExperiments

/-- On the singleton carrier, reflexivity likewise forces equal assigned costs. -/
example (cost : ExperimentCost (Theta := Unit) (X := Unit)) :
    cost (Kernel.id : Kernel Unit Unit) = cost Kernel.id :=
  equal_experiments_have_equal_cost cost rfl

end D5.S3.Estimation.ExperimentCost.BlackwellCostOrthogonality
