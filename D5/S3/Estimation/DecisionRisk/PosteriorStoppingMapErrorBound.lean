/- GID: D5/S3/Estimation/DecisionRisk/PosteriorStoppingMapErrorBound
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/PosteriorStoppingMapErrorBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: MAP output at a posterior threshold has error at most that threshold. -/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/- Library-search audit trail (2026-08-26):
   * Repository searches for `bayes.*error`, `map.*error`, `1 - .*posterior`, and
     posterior-weighted error sums found no theorem stating this stopping guarantee.
     `PosteriorUniversalSufficiency` supplies a finite-weight posterior construction,
     but its theorem concerns equality of conditional values rather than stopped error.
   * Body-shape searches for a history PMF multiplied by a history-indexed posterior
     PMF found no duplicate D5 construction. This module introduces no `def` or
     `abbrev`; its law and posterior arguments use Mathlib's canonical `PMF` carrier.
   * Pinned Mathlib has exact component lemmas `PMF.tsum_coe`, `tsum_fintype`,
     `ENNReal.tsum_le_tsum`, and `ENNReal.tsum_mul_right`, but no exact theorem for
     the complete MAP-at-stopping statement. The proof applies those lemmas directly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ENNReal

noncomputable section

namespace D5.S3.Estimation.DecisionRisk.PosteriorStoppingMapErrorBound

/-- If every stopped history admits a posterior maximizer whose residual mass is at
most `epsilon`, and the reported state is itself posterior-maximal, then the joint
posterior mass assigned to an erroneous report is at most `epsilon`. -/
theorem posterior_stopping_map_error_bound
    {State History : Type*} [Finite State] [DecidableEq State]
    (stoppedHistoryLaw : PMF History)
    (posteriorAtStop : History -> PMF State)
    (estimate : History -> State) (epsilon : ENNReal)
    (mapOutput : forall history state,
      posteriorAtStop history state <= posteriorAtStop history (estimate history))
    (stopped : forall history, exists mapState,
      (forall state,
        posteriorAtStop history state <= posteriorAtStop history mapState) /\
      1 - posteriorAtStop history mapState <= epsilon) :
    (∑' history, stoppedHistoryLaw history *
      ∑' state,
        if estimate history = state then 0 else posteriorAtStop history state) <=
      epsilon := by
  classical
  letI := Fintype.ofFinite State
  have conditional_error_eq (history : History) :
      (∑' state,
        if estimate history = state then 0 else posteriorAtStop history state) =
        1 - posteriorAtStop history (estimate history) := by
    apply ENNReal.eq_sub_of_add_eq' (by simp)
    rw [tsum_fintype]
    calc
      (∑ state,
          if estimate history = state then 0 else posteriorAtStop history state) +
          posteriorAtStop history (estimate history) =
        (∑ state,
          if estimate history = state then 0 else posteriorAtStop history state) +
          ∑ state,
            if estimate history = state then posteriorAtStop history state else 0 := by
              simp
      _ = ∑ state,
          ((if estimate history = state then 0 else posteriorAtStop history state) +
            if estimate history = state then posteriorAtStop history state else 0) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ state, posteriorAtStop history state := by
        apply Finset.sum_congr rfl
        intro state _
        by_cases equalState : estimate history = state <;> simp [equalState]
      _ = ∑' state, posteriorAtStop history state := by rw [tsum_fintype]
      _ = 1 := PMF.tsum_coe (posteriorAtStop history)
  have local_stop (history : History) :
      1 - posteriorAtStop history (estimate history) <= epsilon := by
    obtain ⟨mapState, maximal, belowThreshold⟩ := stopped history
    have equalPosterior :
        posteriorAtStop history (estimate history) =
          posteriorAtStop history mapState :=
      le_antisymm (maximal (estimate history)) (mapOutput history mapState)
    simpa [equalPosterior] using belowThreshold
  calc
    (∑' history, stoppedHistoryLaw history *
        ∑' state,
          if estimate history = state then 0 else posteriorAtStop history state) =
        ∑' history, stoppedHistoryLaw history *
          (1 - posteriorAtStop history (estimate history)) := by
            congr 1
            funext history
            rw [conditional_error_eq]
    _ <= ∑' history, stoppedHistoryLaw history * epsilon := by
      exact ENNReal.tsum_le_tsum fun history =>
        mul_le_mul_of_nonneg_left (local_stop history) (by exact zero_le)
    _ = (∑' history, stoppedHistoryLaw history) * epsilon :=
      ENNReal.tsum_mul_right
    _ = epsilon := by rw [PMF.tsum_coe, one_mul]

#print axioms posterior_stopping_map_error_bound

end D5.S3.Estimation.DecisionRisk.PosteriorStoppingMapErrorBound
