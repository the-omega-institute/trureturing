/- UNCOMPILED same-context, all-branch performance candidate.
Full scalar-table receipts and the whole-checker equivalence are required.
This is the original depth14/fuel7/545-visit suffix, not global acceptance.
-/
import D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerReplay
import D5.S3.Quantum.Entanglement.EJM.EJMCompactCachedProbe14

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerDirectProbe14
open EJMCacheProbe (zeroPath zeroCache zeroPrefix)
open EJMCompactCachedProbe14 (literalPacked packedZero packedZero_wellFormed)

set_option maxHeartbeats 1000000000 in
set_option trace.profiler true in
theorem actual_scalar_lower_suffix :
    EJMPackedLowerReplay.check 7 (zeroPath 14) literalPacked packedZero = true := by
  decide +kernel

theorem actual_original_suffix :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      EJMCacheState.step EJMCacheState.lower EJMGlobalScoreSymmetry.dominates
      EJMPartialBoundData.scale 7 (zeroPath 14) (zeroCache 14) (zeroPrefix 14) = true := by
  have hEq := EJMPackedLowerReplay.check_eq_original 7 (zeroPath 14)
    literalPacked packedZero packedZero_wellFormed (by decide)
  rw [EJMCompactCachedProbe14.literal_decode_exact,
    EJMCompactCachedProbe14.packedZero_decode] at hEq
  exact hEq ▸ actual_scalar_lower_suffix

#print axioms actual_scalar_lower_suffix
#print axioms actual_original_suffix
end D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerDirectProbe14
