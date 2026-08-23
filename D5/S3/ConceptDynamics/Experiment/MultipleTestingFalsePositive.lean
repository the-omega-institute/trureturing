/- GID: D5/S3/ConceptDynamics/Experiment/MultipleTestingFalsePositive
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/MultipleTestingFalsePositive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Independent repeated tests amplify error; every finite family obeys the union bound. -/

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real

/- Library-search audit trail (2026-08-23):
   * Exact pinned-Mathlib hits `ProbabilityTheory.iIndepSet_iff_iIndep`
     and `ProbabilityTheory.iIndep.meas_iInter` compute the probability
     of the intersection of the no-error events; both are applied directly.
   * Exact pinned-Mathlib hits `measure_compl`,
     `measureReal_iUnion_fintype_le`, and `Fin.prod_const` supply the
     complement calculation, the independence-free union bound, and the
     constant finite product.
   * Exact pinned-Mathlib order hits `pow_le_pow_right_of_le_one'` and
     `pow_lt_self_of_lt_one₀` supply monotonicity and strict amplification.
   * Repository searches for false positives, multiple testing,
     independence, and union bounds found no declaration packaging these
     clauses. External `loogle` and `leansearch` are absent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.MultipleTestingFalsePositive

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

/-- For measurable tests of a common false-positive rate, independence gives
the complementary-product formula and hence the exact search-wide error rate.
That rate is monotone in the number of attempts and is strictly larger than
the single-test rate for at least two nondegenerate independent attempts.
Separately, the finite union bound needs no independence hypothesis. -/
theorem at_least_one_false_positive
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (k : Nat) (alpha : Real) (falsePositive : Fin k -> Set Omega)
    (measurable_falsePositive : forall i, MeasurableSet (falsePositive i))
    (single_test_rate : forall i, mu.real (falsePositive i) = alpha)
    (alpha_nonnegative : 0 <= alpha)
    (alpha_le_one : alpha <= 1) :
    (iIndepSet falsePositive mu ->
      mu.real (iInter fun i => (falsePositive i)ᶜ) = (1 - alpha) ^ k /\
      mu.real (iUnion falsePositive) = 1 - (1 - alpha) ^ k /\
      (forall m n : Nat, m <= n ->
        1 - (1 - alpha) ^ m <= 1 - (1 - alpha) ^ n) /\
      (2 <= k -> 0 < alpha -> alpha < 1 ->
        alpha < mu.real (iUnion falsePositive))) /\
    mu.real (iUnion falsePositive) <= (k : Real) * alpha := by
  have union_bound :
      mu.real (iUnion falsePositive) <= (k : Real) * alpha := by
    calc
      mu.real (iUnion falsePositive) <=
          Finset.univ.sum fun i => mu.real (falsePositive i) :=
        measureReal_iUnion_fintype_le falsePositive
      _ = Finset.univ.sum fun _i : Fin k => alpha := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact single_test_rate i
      _ = (k : Real) * alpha := by
        simp [nsmul_eq_mul]
  refine And.intro ?_ union_bound
  intro independent
  have generated_independent :
      iIndep (fun i => MeasurableSpace.generateFrom {falsePositive i}) mu :=
    (iIndepSet_iff_iIndep falsePositive mu).mp independent
  have complement_rate : forall i, mu.real ((falsePositive i)ᶜ) = 1 - alpha := by
    intro i
    rw [probReal_compl_eq_one_sub (measurable_falsePositive i)]
    exact congrArg (fun rate : Real => 1 - rate) (single_test_rate i)
  have no_false_positive :
      mu.real (iInter fun i => (falsePositive i)ᶜ) = (1 - alpha) ^ k := by
    have intersection_measure := generated_independent.meas_iInter fun i =>
      (MeasurableSpace.measurableSet_generateFrom
        (show falsePositive i ∈ ({falsePositive i} : Set (Set Omega)) by simp)).compl
    calc
      mu.real (iInter fun i => (falsePositive i)ᶜ) =
          (Finset.univ.prod fun i => mu ((falsePositive i)ᶜ)).toReal := by
        exact congrArg ENNReal.toReal intersection_measure
      _ = Finset.univ.prod fun i => mu.real ((falsePositive i)ᶜ) := by
        exact ENNReal.toReal_prod Finset.univ fun i => mu ((falsePositive i)ᶜ)
      _ = Finset.univ.prod fun _i : Fin k => (1 - alpha) := by
        apply Finset.prod_congr rfl
        intro i _hi
        exact complement_rate i
      _ = (1 - alpha) ^ k := Fin.prod_const k (1 - alpha)
  have at_least_one :
      mu.real (iUnion falsePositive) = 1 - (1 - alpha) ^ k := by
    rw [iUnion_eq_compl_iInter_compl]
    rw [probReal_compl_eq_one_sub
      (MeasurableSet.iInter fun i => (measurable_falsePositive i).compl)]
    exact congrArg (fun rate : Real => 1 - rate) no_false_positive
  have monotone_attempts : forall m n : Nat, m <= n ->
      1 - (1 - alpha) ^ m <= 1 - (1 - alpha) ^ n := by
    intro m n hmn
    have power_antitone : (1 - alpha) ^ n <= (1 - alpha) ^ m :=
      Bound.pow_le_pow_right_of_le_one_or_one_le
        (Or.inr <| And.intro (sub_nonneg.mpr alpha_le_one)
          (And.intro (by linarith) hmn))
    linarith
  have strict_search_rate : 2 <= k -> 0 < alpha -> alpha < 1 ->
      alpha < mu.real (iUnion falsePositive) := by
    intro hk alpha_pos alpha_lt_one
    have complement_pos : 0 < 1 - alpha := by linarith
    have complement_lt_one : 1 - alpha < (1 : Real) := by linarith
    have power_lt_complement : (1 - alpha) ^ k < 1 - alpha :=
      pow_lt_self_of_lt_one₀ complement_pos complement_lt_one (lt_of_lt_of_le Nat.one_lt_two hk)
    rw [at_least_one]
    linarith
  exact And.intro no_false_positive
    (And.intro at_least_one (And.intro monotone_attempts strict_search_rate))

#print axioms at_least_one_false_positive

end D5.S3.ConceptDynamics.Experiment.MultipleTestingFalsePositive
