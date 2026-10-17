/- Prepared performance sample only. The literal cache receives a full
kernel equality with the actually computed original zero-prefix cache. This
tests materialization costs without changing any subsequent checker semantics,
score, margin, context, incidence, transition or value branch. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCacheMaterialization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMMaterializedCacheProbe18
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe
open D5.S3.Quantum.Entanglement.EJM.EJMCacheMaterialization
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

def literalCache : Cache := ⟨![⟨(15215,(0,0)), EJMTriangleCacheData.mirror 15215⟩,⟨(4590,(6,0)), EJMTriangleCacheData.mirror 4590⟩,⟨(4590,(6,0)), EJMTriangleCacheData.mirror 4590⟩,⟨(0,(6,0)), EJMTriangleCacheData.mirror 0⟩,⟨(15215,(0,0)), EJMTriangleCacheData.mirror 15215⟩,⟨(4590,(6,0)), EJMTriangleCacheData.mirror 4590⟩,⟨(4590,(6,0)), EJMTriangleCacheData.mirror 4590⟩,⟨(0,(0,0)), EJMTriangleCacheData.mirror 0⟩,⟨(15215,(0,0)), EJMTriangleCacheData.mirror 15215⟩,⟨(4590,(6,0)), EJMTriangleCacheData.mirror 4590⟩,⟨(4590,(6,0)), EJMTriangleCacheData.mirror 4590⟩,⟨(0,(0,0)), EJMTriangleCacheData.mirror 0⟩,⟨(0,(0,0)), EJMTriangleCacheData.mirror 0⟩,⟨(12903,(0,0)), EJMTriangleCacheData.mirror 12903⟩,⟨(12903,(0,0)), EJMTriangleCacheData.mirror 12903⟩,⟨(26774,(0,0)), EJMTriangleCacheData.mirror 26774⟩], ![⟨(1200,(0,0)), EJMSingletonCacheData.mirror 1200⟩,⟨(1200,(0,0)), EJMSingletonCacheData.mirror 1200⟩,⟨(1200,(0,0)), EJMSingletonCacheData.mirror 1200⟩,⟨(1200,(0,0)), EJMSingletonCacheData.mirror 1200⟩,⟨(1200,(0,0)), EJMSingletonCacheData.mirror 1200⟩,⟨(1200,(0,0)), EJMSingletonCacheData.mirror 1200⟩,⟨(1200,(0,0)), EJMSingletonCacheData.mirror 1200⟩,⟨(1200,(0,0)), EJMSingletonCacheData.mirror 1200⟩,⟨(1200,(0,0)), EJMSingletonCacheData.mirror 1200⟩,⟨(1200,(0,0)), EJMSingletonCacheData.mirror 1200⟩,⟨(1200,(0,0)), EJMSingletonCacheData.mirror 1200⟩,⟨(1200,(0,0)), EJMSingletonCacheData.mirror 1200⟩,⟨(0,(0,0)), EJMSingletonCacheData.mirror 0⟩,⟨(0,(0,0)), EJMSingletonCacheData.mirror 0⟩,⟨(3297,(0,0)), EJMSingletonCacheData.mirror 3297⟩,⟨(3297,(0,0)), EJMSingletonCacheData.mirror 3297⟩]⟩

set_option maxHeartbeats 100000000 in
-- All thirty-two complete cached states and all row fields are compared with the computed prefix.
set_option trace.profiler true in
private theorem exact_fields : checkSame literalCache (zeroCache 18) = true := by
  decide +kernel

theorem literal_cache_exact : literalCache = zeroCache 18 :=
  checked_same _ _ exact_fields

set_option maxHeartbeats 1000000000 in
-- This unchanged actual subtree checks all 13 original tags and their actual contexts.
set_option trace.profiler true in
theorem actual_zero_suffix :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      step lower EJMGlobalScoreSymmetry.dominates scale 3 (zeroPath 18)
      literalCache (zeroPrefix 18) = true := by
  decide +kernel

/-- Rewrite the complete cache equality to recover the exact original computed-cache check. -/
theorem actual_computed_cache_suffix :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      step lower EJMGlobalScoreSymmetry.dominates scale 3 (zeroPath 18)
      (zeroCache 18) (zeroPrefix 18) = true := by
  simpa only [literal_cache_exact] using actual_zero_suffix

#print axioms literal_cache_exact
#print axioms actual_zero_suffix
#print axioms actual_computed_cache_suffix
end D5.S3.Quantum.Entanglement.EJM.EJMMaterializedCacheProbe18
