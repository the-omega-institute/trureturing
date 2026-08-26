/- GID: D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Expected trials are 1+epsilon; zero and unit errors attain one and two trials. -/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * Current-tree searches found no named adaptive-stopping experiment count or
     expectation theorem in D5, including the adjacent static exact-design module.
   * Pinned Mathlib provides `PMF`, `PMF.integral_eq_sum`, `Finset.sum_congr`,
     `Finset.sum_fin_eq_sum_range`, and the exact-arity lemma `Fin.sum_univ_three`.
   * The exact-arity lemma is used below. A direct PMF-weighted finite sum avoids
     importing measurable-space and Bochner-integral machinery for this calculation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.ExperimentDesign.AdaptiveEarlyStopping

open scoped BigOperators

/-- The model in which the change order is `X` then `Y`. -/
def M_XY : Fin 3 := 0

/-- The null model. -/
def M_0 : Fin 3 := 1

/-- The model in which the change order is `Y` then `X`. -/
def M_YX : Fin 3 := 2

/-- The first experiment, which is positive exactly under `M_XY`. -/
def E_X (model : Fin 3) : Bool := decide (model = M_XY)

/-- The second experiment, which separates `M_0` from `M_YX`. -/
def E_Y (model : Fin 3) : Bool := decide (model = M_YX)

/-- The source prior condition. Only the combined mass outside `M_XY` is fixed,
so its split between `M_0` and `M_YX` is deliberately unconstrained. -/
def IsAdaptivePrior (prior : PMF (Fin 3)) (epsilon : Real) : Prop :=
  (prior M_XY).toReal = 1 - epsilon ∧
    (prior M_0).toReal + (prior M_YX).toReal = epsilon

/-- The number of experiments executed by the adaptive protocol: one after a
positive first result and two otherwise. This is an execution count, not a general cost. -/
def experimentCount (model : Fin 3) : Real :=
  if E_X model then 1 else 2

/-- The finite PMF-weighted expectation of the protocol's execution count. -/
def expectedExperimentCount (prior : PMF (Fin 3)) : Real :=
  ∑ model, (prior model).toReal * experimentCount model

/-- Nonnegative remaining masses force their prescribed total to be nonnegative. -/
theorem error_probability_nonnegative
    (prior : PMF (Fin 3)) (epsilon : Real)
    (hremaining : (prior M_0).toReal + (prior M_YX).toReal = epsilon) :
    0 ≤ epsilon := by
  have hM0 : 0 ≤ (prior M_0).toReal := ENNReal.toReal_nonneg
  have hMYX : 0 ≤ (prior M_YX).toReal := ENNReal.toReal_nonneg
  linarith
#print axioms error_probability_nonnegative

/-- Under the source prior, the expected number of executed experiments is
exactly `1 + epsilon`, independently of the remaining-mass split. -/
theorem expected_experiment_count_eq_one_add
    (prior : PMF (Fin 3)) (epsilon : Real)
    (hprior : IsAdaptivePrior prior epsilon) :
    expectedExperimentCount prior = 1 + epsilon := by
  rcases hprior with ⟨hXY, hremaining⟩
  simp [expectedExperimentCount, experimentCount, E_X, M_XY, M_0, M_YX,
    Fin.sum_univ_three] at hXY hremaining ⊢
  linarith
#print axioms expected_experiment_count_eq_one_add

/-- If the error probability is strictly below one, adaptive stopping uses
strictly fewer than two experiments in expectation. -/
theorem expected_experiment_count_lt_two
    (prior : PMF (Fin 3)) (epsilon : Real)
    (hprior : IsAdaptivePrior prior epsilon) (hepsilon : epsilon < 1) :
    expectedExperimentCount prior < 2 := by
  rw [expected_experiment_count_eq_one_add prior epsilon hprior]
  linarith
#print axioms expected_experiment_count_lt_two

/-- At zero error probability the prior is concentrated on `M_XY`, and the
expected execution count is exactly one. -/
theorem zero_error_probability_expected_count :
    IsAdaptivePrior (PMF.pure M_XY) 0 ∧
      expectedExperimentCount (PMF.pure M_XY) = 1 := by
  simp [IsAdaptivePrior, expectedExperimentCount, experimentCount, E_X, M_XY, M_0,
    M_YX, Fin.sum_univ_three, PMF.pure_apply]
#print axioms zero_error_probability_expected_count

/-- The strict hypothesis `epsilon < 1` is necessary: at unit error mass the
prior concentrated on `M_0` has expectation two, so the strict bound is false. -/
theorem error_probability_lt_one_is_necessary :
    IsAdaptivePrior (PMF.pure M_0) 1 ∧
      expectedExperimentCount (PMF.pure M_0) = 2 ∧
        ¬expectedExperimentCount (PMF.pure M_0) < 2 := by
  simp [IsAdaptivePrior, expectedExperimentCount, experimentCount, E_X, M_XY, M_0,
    M_YX, Fin.sum_univ_three, PMF.pure_apply]
#print axioms error_probability_lt_one_is_necessary

/-- Allocating all remaining mass to either `M_0` or `M_YX` leaves the unit-error
expectation unchanged, confirming that only their combined mass matters. -/
theorem extreme_remaining_allocations_same_expectation :
    IsAdaptivePrior (PMF.pure M_0) 1 ∧
      IsAdaptivePrior (PMF.pure M_YX) 1 ∧
        expectedExperimentCount (PMF.pure M_0) = 2 ∧
          expectedExperimentCount (PMF.pure M_YX) = 2 := by
  simp [IsAdaptivePrior, expectedExperimentCount, experimentCount, E_X, M_XY, M_0,
    M_YX, Fin.sum_univ_three, PMF.pure_apply]
#print axioms extreme_remaining_allocations_same_expectation

end D5.S3.ConceptDynamics.ExperimentDesign.AdaptiveEarlyStopping
