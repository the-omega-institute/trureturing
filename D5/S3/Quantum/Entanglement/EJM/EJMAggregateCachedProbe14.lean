/- Performance sample of the original depth-14, fuel-7 subtree. The scalar
total must earn its equality to the complete original 32-block sum. The
545-tag sample retains every original branch and symmetry context; it is
not an acceptance theorem for the full global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMAggregateReplay
import D5.S3.Quantum.Entanglement.EJM.EJMCompactCachedProbe14

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Quantum.Entanglement.EJM.EJMAggregateCachedProbe14

open EJMCacheProbe (zeroPath zeroCache zeroPrefix)
open EJMCompactCachedProbe14

def literalAggregate : EJMAggregateCachePacking.AggregateCache :=
  ⟨literalPacked, -97388108049871275⟩

set_option maxHeartbeats 100000000 in
-- Compute the exact complete 32-block scalar sum before using the cache.
set_option trace.profiler true in
theorem literal_valid : EJMAggregateCachePacking.Valid literalAggregate := by
  unfold EJMAggregateCachePacking.Valid
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- Reduce all 545 actual tags, including every value branch and symmetry leaf.
set_option trace.profiler true in
theorem actual_aggregate_suffix :
    EJMAggregateReplay.check 7 (zeroPath 14) literalAggregate packedZero = true := by
  decide +kernel

theorem actual_original_suffix :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      EJMCacheState.step EJMCacheState.lower EJMGlobalScoreSymmetry.dominates
      EJMPartialBoundData.scale 7 (zeroPath 14) (zeroCache 14) (zeroPrefix 14) = true := by
  have hEq := EJMAggregateReplay.check_eq_original 7 (zeroPath 14)
    literalAggregate literal_valid packedZero packedZero_wellFormed (by decide)
  change EJMAggregateReplay.check 7 (zeroPath 14) literalAggregate packedZero =
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      EJMCacheState.step EJMCacheState.lower EJMGlobalScoreSymmetry.dominates
      EJMPartialBoundData.scale 7 (zeroPath 14) (EJMCachePacking.decode literalPacked)
      (EJMCompactPartial.decode packedZero) at hEq
  rw [literal_decode_exact, packedZero_decode] at hEq
  exact hEq ▸ actual_aggregate_suffix

#print axioms literal_valid
#print axioms actual_aggregate_suffix
#print axioms actual_original_suffix

end D5.S3.Quantum.Entanglement.EJM.EJMAggregateCachedProbe14
