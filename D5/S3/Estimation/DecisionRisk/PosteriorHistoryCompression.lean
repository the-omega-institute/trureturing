/- GID: D5/S3/Estimation/DecisionRisk/PosteriorHistoryCompression
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/PosteriorHistoryCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A posterior measure determines prediction, risk, policy cost, and continuation value. -/

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/- Library-search audit trail (2026-08-26):
   * The frozen theorem `posterior_future_policy_universal_sufficiency` is a
     finite hidden-state specialization exposing only a terminal Bayes value;
     it omits separate public prediction and policy-cost clauses, so it is not
     an exact bind for this atom.
   * Repository searches for equal posterior measures together with prediction,
     Bayes risk, every future-policy cost, and optimal continuation value found
     no D5 theorem carrying all four public clauses.
   * Pinned Mathlib's `Measure`, `lintegral`, and complete-lattice infimum are the
     canonical primitives used directly. No new `def` or `abbrev` is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace D5.S3.Estimation.DecisionRisk.PosteriorHistoryCompression

/-- When future event probabilities and continuation costs are conditioned only
on the hidden state and the selected experiment or policy, equal posterior
measures make the complete prediction, Bayes-risk, policy-cost, and optimal
continuation outputs independent of the histories that produced them. -/
theorem posterior_history_compression
    {Hidden History Experiment Event Policy Action : Type*}
    [MeasurableSpace Hidden]
    (posterior : History -> Measure Hidden)
    (futureEventProbability : Experiment -> Event -> Hidden -> ENNReal)
    (policyCost : Policy -> Hidden -> ENNReal)
    (loss : Action -> Hidden -> ENNReal)
    {history history' : History}
    (equalPosterior : posterior history = posterior history') :
    (forall experiment event,
      (∫⁻ hidden, futureEventProbability experiment event hidden ∂posterior history) =
        ∫⁻ hidden, futureEventProbability experiment event hidden ∂posterior history') ∧
      ((⨅ action, ∫⁻ hidden, loss action hidden ∂posterior history) =
        ⨅ action, ∫⁻ hidden, loss action hidden ∂posterior history') ∧
      (forall policy,
        (∫⁻ hidden, policyCost policy hidden ∂posterior history) =
          ∫⁻ hidden, policyCost policy hidden ∂posterior history') ∧
      ((⨅ policy, ∫⁻ hidden, policyCost policy hidden ∂posterior history) =
        ⨅ policy, ∫⁻ hidden, policyCost policy hidden ∂posterior history') := by
  constructor
  · intro experiment event
    rw [equalPosterior]
  constructor
  · rw [equalPosterior]
  constructor
  · intro policy
    rw [equalPosterior]
  · rw [equalPosterior]

#print axioms posterior_history_compression

end D5.S3.Estimation.DecisionRisk.PosteriorHistoryCompression
