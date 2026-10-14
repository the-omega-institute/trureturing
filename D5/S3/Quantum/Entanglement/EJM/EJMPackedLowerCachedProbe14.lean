/- The same complete 545-tag performance sample with an exact scalar
lookup representation. Its full-domain scalar receipts and whole-checker
bridge are required; no full global certificate acceptance is asserted. -/

import D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerAggregate
import D5.S3.Quantum.Entanglement.EJM.EJMAggregateCachedProbe14

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerCachedProbe14

open EJMCacheProbe (zeroPath zeroCache zeroPrefix)
open EJMCompactCachedProbe14 (packedZero)
open EJMAggregateCachedProbe14 (literalAggregate)

set_option maxHeartbeats 1000000000 in
-- Reduce the unchanged complete suffix with the fully checked scalar table.
set_option trace.profiler true in
theorem actual_packed_lower_suffix :
    EJMCompactDominates.checkFast EJMPackedLowerAggregate.step
      EJMAggregateCachePacking.lower EJMPartialBoundData.scale
      7 (zeroPath 14) literalAggregate packedZero = true := by
  decide +kernel

theorem actual_original_suffix :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      EJMCacheState.step EJMCacheState.lower EJMGlobalScoreSymmetry.dominates
      EJMPartialBoundData.scale 7 (zeroPath 14) (zeroCache 14) (zeroPrefix 14) = true := by
  have accepted := actual_packed_lower_suffix
  have hstep : EJMPackedLowerAggregate.step = EJMAggregateCachePacking.step := by
    funext cache g a
    exact EJMPackedLowerAggregate.step_eq cache g a
  rw [hstep] at accepted
  have hEq := EJMAggregateReplay.check_eq_original 7 (zeroPath 14)
    literalAggregate EJMAggregateCachedProbe14.literal_valid packedZero
    EJMCompactCachedProbe14.packedZero_wellFormed (by decide)
  change EJMAggregateReplay.check 7 (zeroPath 14) literalAggregate packedZero =
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      EJMCacheState.step EJMCacheState.lower EJMGlobalScoreSymmetry.dominates
      EJMPartialBoundData.scale 7 (zeroPath 14)
      (EJMCachePacking.decode EJMCompactCachedProbe14.literalPacked)
      (EJMCompactPartial.decode packedZero) at hEq
  rw [EJMCompactCachedProbe14.literal_decode_exact,
    EJMCompactCachedProbe14.packedZero_decode] at hEq
  exact hEq ▸ accepted

#print axioms actual_packed_lower_suffix
#print axioms actual_original_suffix

end D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerCachedProbe14
