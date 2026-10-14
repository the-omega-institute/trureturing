/- Prepared compact-partial runtime sample only.  The depth18 prefix is
stored as `(depth, digits)` with the complete actual zero-prefix context,
the original cache, margin, nodes and all four recursive values. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCompactPartial
import D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Quantum.Entanglement.EJM.EJMCompactPartialProbe18
open D5.S3.Quantum.Entanglement.EJM.EJMCompactPartial
open D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe

def packedZero : PackedPartial := ⟨18, 0⟩

theorem packedZero_wellFormed : WellFormed packedZero := by
  constructor <;> decide

theorem packedZero_decode : decode packedZero = zeroPrefix 18 := by
  funext g
  by_cases h : g.val < 18 <;> simp [packedZero, decode, zeroPrefix, h]

/- The following is an uncompiled kernel-check candidate.  It keeps the
original depth18/fuel3 subtree and all original branches. -/
set_option maxHeartbeats 1000000000 in
theorem actual_compact_suffix :
    checkPacked EJMGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
      EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
      3 (zeroPath 18) (zeroCache 18) packedZero = true := by
  decide +kernel

theorem actual_original_suffix :
    check EJMGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
      EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
      3 (zeroPath 18) (zeroCache 18) (zeroPrefix 18) = true := by
  have hEq := checkPacked_eq_original 3 (zeroPath 18) (zeroCache 18) packedZero
    packedZero_wellFormed (by decide)
  rw [packedZero_decode] at hEq
  exact (hEq ▸ actual_compact_suffix)

#print axioms packedZero_decode
#print axioms actual_compact_suffix
#print axioms actual_original_suffix
end D5.S3.Quantum.Entanglement.EJM.EJMCompactPartialProbe18
