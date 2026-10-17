/- Prepared performance sample only. The literal cache receives a full
kernel equality with the actually computed original zero-prefix cache. This
tests materialization costs without changing any subsequent checker semantics,
score, margin, context, incidence, transition or value branch. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCacheMaterialization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMMaterializedCacheProbe10
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe
open D5.S3.Quantum.Entanglement.EJM.EJMCacheMaterialization
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

def literalCache : Cache := ⟨![⟨(40768,(0,0)), EJMTriangleCacheData.mirror 40768⟩,⟨(39362,(6,0)), EJMTriangleCacheData.mirror 39362⟩,⟨(39362,(6,0)), EJMTriangleCacheData.mirror 39362⟩,⟨(35402,(6,0)), EJMTriangleCacheData.mirror 35402⟩,⟨(35402,(0,0)), EJMTriangleCacheData.mirror 35402⟩,⟨(39731,(0,0)), EJMTriangleCacheData.mirror 39731⟩,⟨(39731,(0,0)), EJMTriangleCacheData.mirror 39731⟩,⟨(41062,(0,0)), EJMTriangleCacheData.mirror 41062⟩,⟨(41062,(6,0)), EJMTriangleCacheData.mirror 41062⟩,⟨(40472,(6,0)), EJMTriangleCacheData.mirror 40472⟩,⟨(40472,(6,0)), EJMTriangleCacheData.mirror 40472⟩,⟨(38858,(0,0)), EJMTriangleCacheData.mirror 38858⟩,⟨(41062,(6,0)), EJMTriangleCacheData.mirror 41062⟩,⟨(40472,(6,0)), EJMTriangleCacheData.mirror 40472⟩,⟨(40472,(6,0)), EJMTriangleCacheData.mirror 40472⟩,⟨(38858,(0,0)), EJMTriangleCacheData.mirror 38858⟩], ![⟨(8425,(0,0)), EJMSingletonCacheData.mirror 8425⟩,⟨(8425,(0,0)), EJMSingletonCacheData.mirror 8425⟩,⟨(8425,(0,0)), EJMSingletonCacheData.mirror 8425⟩,⟨(8425,(0,0)), EJMSingletonCacheData.mirror 8425⟩,⟨(7715,(0,0)), EJMSingletonCacheData.mirror 7715⟩,⟨(7715,(0,0)), EJMSingletonCacheData.mirror 7715⟩,⟨(8500,(0,0)), EJMSingletonCacheData.mirror 8500⟩,⟨(8500,(0,0)), EJMSingletonCacheData.mirror 8500⟩,⟨(8125,(0,0)), EJMSingletonCacheData.mirror 8125⟩,⟨(8125,(0,0)), EJMSingletonCacheData.mirror 8125⟩,⟨(8125,(0,0)), EJMSingletonCacheData.mirror 8125⟩,⟨(8125,(0,0)), EJMSingletonCacheData.mirror 8125⟩,⟨(8125,(0,0)), EJMSingletonCacheData.mirror 8125⟩,⟨(8125,(0,0)), EJMSingletonCacheData.mirror 8125⟩,⟨(8125,(0,0)), EJMSingletonCacheData.mirror 8125⟩,⟨(8125,(0,0)), EJMSingletonCacheData.mirror 8125⟩]⟩

set_option maxHeartbeats 100000000 in
-- All thirty-two complete cached states and all row fields are compared with the computed prefix.
set_option trace.profiler true in
private theorem exact_fields : checkSame literalCache (zeroCache 10) = true := by
  decide +kernel

theorem literal_cache_exact : literalCache = zeroCache 10 :=
  checked_same _ _ exact_fields

set_option maxHeartbeats 1000000000 in
-- This unchanged actual subtree checks all 18937 original tags and their actual contexts.
set_option trace.profiler true in
theorem actual_zero_suffix :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      step lower EJMGlobalScoreSymmetry.dominates scale 11 (zeroPath 10)
      literalCache (zeroPrefix 10) = true := by
  decide +kernel

/-- Rewrite the complete cache equality to recover the exact original computed-cache check. -/
theorem actual_computed_cache_suffix :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      step lower EJMGlobalScoreSymmetry.dominates scale 11 (zeroPath 10)
      (zeroCache 10) (zeroPrefix 10) = true := by
  simpa only [literal_cache_exact] using actual_zero_suffix

#print axioms literal_cache_exact
#print axioms actual_zero_suffix
#print axioms actual_computed_cache_suffix
end D5.S3.Quantum.Entanglement.EJM.EJMMaterializedCacheProbe10
