/- GID: D5/S1/Words/Patterns/Separable/EndpointCycleHazardAccumulation
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/EndpointCycleHazardAccumulation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The actual shifted hazards diverge and shifted hits recur almost surely. -/

import D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries
import D5.S1.Words.Patterns.Separable.EndpointQuadraticMarginal
import D5.S1.Words.Patterns.Separable.EndpointPredictableHazard
import D5.S1.Words.Patterns.Separable.EndpointCycleHazardSeries
import D5.S1.Words.Patterns.Separable.OccupiedLogEnvelope

/-! The raw occupation term already supplies enough total hazard for the
actual marked-cycle stream, for every integer initial discrepancy. -/

namespace D5.S1.Words.Patterns.Separable.EndpointCycleHazardAccumulation

open D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries
open ActualCycles ActualCycleLaw EndpointCanonicalCycle EndpointFirstCycleHitLimit
open EndpointCycleHazard EndpointPredictableHazard EndpointQuadraticMarginal OccupiedLogEnvelope
open MeasureTheory
open scoped ENNReal

private theorem measurable_shifted_discrepancy (e : ℤ) (j : ℕ) :
    Measurable (fun ω : Stream => e + streamDiscrepancy j ω) := by
  let g (ω : Stream) (i : Fin j) : MarkedCycle := ω i.val
  let f (x : Fin j → MarkedCycle) : ℤ := e + ∑ i : Fin j, discrepancyDelta (x i).2
  exact (measurable_of_countable f).comp
    (show Measurable g from measurable_pi_iff.2 fun i => measurable_pi_apply i.val)

/-- Both conclusions hold on one full-measure event for each initial integer
discrepancy. The hit is tested on the actual marked cycle at the later index. -/
theorem actual_hazard_accumulation_and_recurrence (e : ℤ) :
    ∀ᵐ ω ∂streamMeasure,
      (∑' j, nextHazard (e + streamDiscrepancy j ω)) = ∞ ∧
        ∀ N : ℕ, ∃ k ≥ N, ω ∈ hitAt e k := by
  have hprofile : ∀ᵐ ω ∂streamMeasure,
      ∑' j, ENNReal.ofReal (discrepancyProfile (e + streamDiscrepancy j ω)) = ∞ := by
    apply ae_tsum_discrepancyProfile_eq_top streamMeasure (fun j ω => e + streamDiscrepancy j ω)
      (measurable_shifted_discrepancy e)
    intro δ hδ
    refine ⟨|(e : ℝ)| + (max 1 (20 / δ)) ^ 2, fun j => ?_⟩
    simpa only [shiftedMagnitude] using actual_uniform_quadratic_marginal e δ hδ j
  obtain ⟨t, ht, hbound⟩ := actual_raw_occupation_log_envelope
  have hhaz : ∀ᵐ ω ∂streamMeasure, ∑' j, nextHazard (e + streamDiscrepancy j ω) = ∞ := by
    filter_upwards [hprofile] with ω hω
    apply top_unique
    calc
      ∞ = ENNReal.ofReal t * (∑' j, ENNReal.ofReal
            (discrepancyProfile (e + streamDiscrepancy j ω))) := by
          rw [hω, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr ht))]
      _ = ∑' j, ENNReal.ofReal t * ENNReal.ofReal
          (discrepancyProfile (e + streamDiscrepancy j ω)) := ENNReal.tsum_mul_left.symm
      _ ≤ ∑' j, nextHazard (e + streamDiscrepancy j ω) := by
        apply ENNReal.tsum_le_tsum
        intro j
        let z := e + streamDiscrepancy j ω
        change ENNReal.ofReal t * ENNReal.ofReal (discrepancyProfile z) ≤ nextHazard z
        rw [← ENNReal.ofReal_mul ht.le, nextHazard_eq_normalized_series]
        exact (ENNReal.ofReal_le_ofReal (hbound z).1).trans le_self_add
  exact hhaz.and ((actual_predictable_hazard_and_recurrence e).2 hhaz)

#print axioms actual_hazard_accumulation_and_recurrence

end D5.S1.Words.Patterns.Separable.EndpointCycleHazardAccumulation
