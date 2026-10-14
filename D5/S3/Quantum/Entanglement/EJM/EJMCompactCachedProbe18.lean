/- Prepared performance sample of the unchanged depth18/fuel3 subtree.
The two numeric words must earn an equality to the original computed cache.
Every original branch, row field, partial coordinate and margin is retained.
No full-replay acceptance is asserted by this sample. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCompactCachedReplay
import D5.S3.Quantum.Entanglement.EJM.EJMCacheProbeContext

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Quantum.Entanglement.EJM.EJMCompactCachedProbe18
open D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe
open D5.S3.Quantum.Entanglement.EJM.EJMCompactPartial
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)

def literalPacked : EJMCachePacking.PackedCache :=
  ⟨0x344b000c99c0064ce00000000000024047b92023dc003b6f00000024047b92023dc003b6f48000024047b92023dc003b6f,
   0x670800338400000000000000025800012c00009600004b000025800012c00009600004b000025800012c00009600004b0⟩

theorem zeroCache_rowsCurrent (depth : ℕ) :
    EJMCachePacking.RowsCurrent (zeroCache depth) := by
  induction depth with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ depth ih => exact EJMCachePacking.rowsCurrent_step _ ih _ _

set_option maxHeartbeats 100000000 in
set_option trace.profiler true in
private theorem literal_encoded : literalPacked = EJMCachePacking.encode (zeroCache 18) := by
  decide +kernel

theorem literal_decode_exact : EJMCachePacking.decode literalPacked = zeroCache 18 := by
  rw [literal_encoded]
  exact EJMCachePacking.decode_encode _ (zeroCache_rowsCurrent 18)

def packedZero : PackedPartial := ⟨18, 0⟩

theorem packedZero_wellFormed : WellFormed packedZero := by
  constructor <;> decide

theorem packedZero_decode : decode packedZero = zeroPrefix 18 := by
  funext g
  by_cases h : g.val < 18 <;> simp [packedZero, decode, zeroPrefix, h]

set_option maxHeartbeats 1000000000 in
set_option trace.profiler true in
theorem actual_packed_suffix :
    checkPacked EJMGlobalDAGData.nodes EJMCachePacking.step EJMCachePacking.lower
      EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
      3 (zeroPath 18) literalPacked packedZero = true := by
  decide +kernel

theorem actual_original_suffix :
    check EJMGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
      EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
      3 (zeroPath 18) (zeroCache 18) (zeroPrefix 18) = true := by
  have hEq := EJMCompactCachedReplay.replay_eq_original 3 (zeroPath 18)
    literalPacked packedZero packedZero_wellFormed (by decide)
  rw [literal_decode_exact, packedZero_decode] at hEq
  exact hEq ▸ actual_packed_suffix

#print axioms literal_decode_exact
#print axioms actual_packed_suffix
#print axioms actual_original_suffix

end D5.S3.Quantum.Entanglement.EJM.EJMCompactCachedProbe18
