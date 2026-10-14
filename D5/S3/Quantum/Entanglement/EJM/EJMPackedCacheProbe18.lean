/- Prepared actual-context performance sample only. Two literal
numeric vectors retain all 32 row/action states. The equality check includes
the full hash, lower, slots and future-transition edges of every decoded row.
The depth18/fuel3 suffix retains all 13 actual tags and all four
values, with exactly the original partial context and dominance checker.
Packing has not been measured; no speedup or full acceptance is claimed. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCachePacking
import D5.S3.Quantum.Entanglement.EJM.EJMMaterializedCacheProbe18

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Quantum.Entanglement.EJM.EJMPackedCacheProbe18
open D5.S3.Quantum.Entanglement.EJM.EJMCachePacking
open D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe
open D5.S3.Quantum.Entanglement.EJM.EJMCacheMaterialization
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

def literalPacked : PackedCache := ⟨0x344b000c99c0064ce00000000000024047b92023dc003b6f00000024047b92023dc003b6f48000024047b92023dc003b6f, 0x670800338400000000000000025800012c00009600004b000025800012c00009600004b000025800012c00009600004b0⟩

set_option maxHeartbeats 100000000 in
-- Full fields are checked, including both action coordinates and future edges.
set_option trace.profiler true in
private theorem exact_fields :
    checkSame (decode literalPacked) EJMMaterializedCacheProbe18.literalCache = true := by
  decide +kernel

theorem literal_decode_exact : decode literalPacked = zeroCache 18 :=
  (checked_same _ _ exact_fields).trans EJMMaterializedCacheProbe18.literal_cache_exact

set_option maxHeartbeats 1000000000 in
-- Same nodes, actual p, arithmetic margin and all original value branches.
set_option trace.profiler true in
theorem actual_zero_suffix :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      step lower EJMGlobalScoreSymmetry.dominates scale 3 (zeroPath 18)
      literalPacked (zeroPrefix 18) = true := by
  decide +kernel

/-- Complete checker equality transfers this sample to the original actual cache. -/
theorem actual_decoded_cache_suffix :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      EJMCacheState.step EJMCacheState.lower EJMGlobalScoreSymmetry.dominates scale
      3 (zeroPath 18) (zeroCache 18) (zeroPrefix 18) = true := by
  have accepted := actual_zero_suffix
  rw [check_decode, literal_decode_exact] at accepted
  exact accepted

#print axioms literal_decode_exact
#print axioms actual_zero_suffix
#print axioms actual_decoded_cache_suffix
end D5.S3.Quantum.Entanglement.EJM.EJMPackedCacheProbe18
