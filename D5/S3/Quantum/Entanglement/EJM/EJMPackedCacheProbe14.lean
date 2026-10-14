/- Prepared actual-context performance sample only. Two literal
numeric vectors retain all 32 row/action states. The equality check includes
the full hash, lower, slots and future-transition edges of every decoded row.
The depth14/fuel7 suffix retains all 545 actual tags and all four
values, with exactly the original partial context and dominance checker.
Packing has not been measured; no speedup or full acceptance is claimed. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCachePacking
import D5.S3.Quantum.Entanglement.EJM.EJMMaterializedCacheProbe14

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Quantum.Entanglement.EJM.EJMPackedCacheProbe14
open D5.S3.Quantum.Entanglement.EJM.EJMCachePacking
open D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe
open D5.S3.Quantum.Entanglement.EJM.EJMCacheMaterialization
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

def literalPacked : PackedCache := ⟨0x344b2421fb5210fda0097ca004be5001e58c00f2c6003b6f001db7a41a7cd20d3e6008a4a481db7a41a7cd20d3e6008a4a, 0xae5800572c002b960015cb000dfd8006fec001c76000e3b000c090006048003024001812000c090006048003024001812⟩

set_option maxHeartbeats 100000000 in
-- Full fields are checked, including both action coordinates and future edges.
set_option trace.profiler true in
private theorem exact_fields :
    checkSame (decode literalPacked) EJMMaterializedCacheProbe14.literalCache = true := by
  decide +kernel

theorem literal_decode_exact : decode literalPacked = zeroCache 14 :=
  (checked_same _ _ exact_fields).trans EJMMaterializedCacheProbe14.literal_cache_exact

set_option maxHeartbeats 1000000000 in
-- Same nodes, actual p, arithmetic margin and all original value branches.
set_option trace.profiler true in
theorem actual_zero_suffix :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      step lower EJMGlobalScoreSymmetry.dominates scale 7 (zeroPath 14)
      literalPacked (zeroPrefix 14) = true := by
  decide +kernel

/-- Complete checker equality transfers this sample to the original actual cache. -/
theorem actual_decoded_cache_suffix :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      EJMCacheState.step EJMCacheState.lower EJMGlobalScoreSymmetry.dominates scale
      7 (zeroPath 14) (zeroCache 14) (zeroPrefix 14) = true := by
  have accepted := actual_zero_suffix
  rw [check_decode, literal_decode_exact] at accepted
  exact accepted

#print axioms literal_decode_exact
#print axioms actual_zero_suffix
#print axioms actual_decoded_cache_suffix
end D5.S3.Quantum.Entanglement.EJM.EJMPackedCacheProbe14
