/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69ActualSeedBounds
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69ActualSeedBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69BasisEndpoint.mixedUnitaryRank; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69Bounds.strict_inclusion
   digest: Actual seed enclosures complete the order-69 root-existence proof. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped69AnalyticOrders
import D5.S3.Quantum.QuantumChannels.WernerHolevo.ChirpedActualSeedBounds
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Fintype.EquivFin

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Chirped69

local instance : NeZero n := ⟨dimension_pos.ne'⟩

theorem seedBounds : ChirpedReplay.CorrelationRows.SeedBounds rows (exactRows center) := by
  refine ChirpedActualSeedBounds.rows_of_seed_specs (count := seeds.length)
    dimension_pos inverseMultiplier pick seed seedAt seedSlopeAt rootAt phaseAt slopeAt
    (fun i => signEntry i.val) center ?_ ?_ ?_ ?_ rootAt_error ?_ ?_
  · exact fun k => valid_seed k.val k.isLt
  · intro k
    change Fin 4 at k
    fin_cases k <;> exact Or.inr ⟨_, rfl⟩
  · intro i
    exact constraints_domain ⟨(equation i.val).1, equation_domain i⟩
  · exact fun k d => seed_spec k.val k.isLt d.val d.isLt
  · intro j
    simpa only [ChirpedAnalyticDrift.ReplayBridge.phaseAt, ChirpedAnalyticDrift.ReplayBridge.slopeAt,
      dif_pos j.isLt] using phaseSlope_error j
  · exact fun i => (signs_unit i).symm

theorem existsUnique_zero_closedBall :
    ∃! x, x ∈ Metric.closedBall center ChirpedReplay.radius ∧ F x = 0 :=
  existsUnique_zero_of_seedBounds seedBounds

end Chirped69
