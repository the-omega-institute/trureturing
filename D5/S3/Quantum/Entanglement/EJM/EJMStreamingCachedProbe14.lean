/- Prepared performance sample of the unchanged depth14/fuel7 subtree.
The two numeric words must earn an equality to the original computed cache.
Every original branch, row field, partial coordinate and margin is retained.
No full-replay acceptance is asserted by this sample. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCompactCachedReplay
import D5.S3.Quantum.Entanglement.EJM.EJMStreamingCachePacking
import D5.S3.Quantum.Entanglement.EJM.EJMCacheProbeContext

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Quantum.Entanglement.EJM.EJMStreamingCachedProbe14
open D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe
open D5.S3.Quantum.Entanglement.EJM.EJMCompactPartial
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)

def literalPacked : EJMCachePacking.PackedCache :=
  ⟨0x344b2421fb5210fda0097ca004be5001e58c00f2c6003b6f001db7a41a7cd20d3e6008a4a481db7a41a7cd20d3e6008a4a,
   0xae5800572c002b960015cb000dfd8006fec001c76000e3b000c090006048003024001812000c090006048003024001812⟩

private theorem zeroCache_rowsCurrent (depth : ℕ) :
    EJMCachePacking.RowsCurrent (zeroCache depth) := by
  induction depth with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ depth ih => exact EJMCachePacking.rowsCurrent_step _ ih _ _

set_option maxHeartbeats 100000000 in
-- Check both original packed numeric vectors by actual kernel reduction.
set_option trace.profiler true in
private theorem literal_encoded : literalPacked = EJMCachePacking.encode (zeroCache 14) := by
  decide +kernel

theorem literal_decode_exact : EJMCachePacking.decode literalPacked = zeroCache 14 := by
  rw [literal_encoded]
  exact EJMCachePacking.decode_encode _ (zeroCache_rowsCurrent 14)

def packedZero : PackedPartial := ⟨14, 0⟩

theorem packedZero_wellFormed : WellFormed packedZero := by
  constructor <;> decide

theorem packedZero_decode : decode packedZero = zeroPrefix 14 := by
  funext g
  by_cases h : g.val < 18 <;> simp [packedZero, decode, zeroPrefix, h]

set_option maxHeartbeats 1000000000 in
-- Check the complete original finite suffix, retaining all four value branches.
set_option trace.profiler true in
theorem actual_packed_suffix :
    checkPacked EJMGlobalDAGData.nodes EJMStreamingCachePacking.step EJMStreamingCachePacking.lower
      EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
      7 (zeroPath 14) literalPacked packedZero = true := by
  decide +kernel

theorem actual_original_suffix :
    check EJMGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
      EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
      7 (zeroPath 14) (zeroCache 14) (zeroPrefix 14) = true := by
  have hEq := EJMCompactCachedReplay.replay_eq_original 7 (zeroPath 14)
    literalPacked packedZero packedZero_wellFormed (by decide)
  rw [literal_decode_exact, packedZero_decode] at hEq
  have accepted := actual_packed_suffix
  have hstep : EJMStreamingCachePacking.step = EJMCachePacking.step := by
    funext cache g a
    exact EJMStreamingCachePacking.step_eq_original cache g a
  have hlower : EJMStreamingCachePacking.lower = EJMCachePacking.lower := by
    funext cache
    exact EJMStreamingCachePacking.lower_eq_original cache
  rw [hstep, hlower] at accepted
  exact hEq ▸ accepted

#print axioms literal_decode_exact
#print axioms actual_packed_suffix
#print axioms actual_original_suffix

end D5.S3.Quantum.Entanglement.EJM.EJMStreamingCachedProbe14
