/- Prepared performance sample only. The literal cache receives a full
kernel equality with the actually computed original zero-prefix cache. This
tests materialization costs without changing any subsequent checker semantics,
score, margin, context, incidence, transition or value branch. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCacheMaterialization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMMaterializedCacheProbe14
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe
open D5.S3.Quantum.Entanglement.EJM.EJMCacheMaterialization
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

def literalCache : Cache := ⟨![⟨(35402,(0,0)), EJMTriangleCacheData.mirror 35402⟩,⟨(27123,(6,0)), EJMTriangleCacheData.mirror 27123⟩,⟨(27123,(6,0)), EJMTriangleCacheData.mirror 27123⟩,⟨(15215,(6,0)), EJMTriangleCacheData.mirror 15215⟩,⟨(35402,(0,0)), EJMTriangleCacheData.mirror 35402⟩,⟨(27123,(6,0)), EJMTriangleCacheData.mirror 27123⟩,⟨(27123,(6,0)), EJMTriangleCacheData.mirror 27123⟩,⟨(15215,(0,0)), EJMTriangleCacheData.mirror 15215⟩,⟨(15215,(0,0)), EJMTriangleCacheData.mirror 15215⟩,⟨(31075,(0,0)), EJMTriangleCacheData.mirror 31075⟩,⟨(31075,(0,0)), EJMTriangleCacheData.mirror 31075⟩,⟨(38858,(0,0)), EJMTriangleCacheData.mirror 38858⟩,⟨(38858,(0,0)), EJMTriangleCacheData.mirror 38858⟩,⟨(34797,(6,0)), EJMTriangleCacheData.mirror 34797⟩,⟨(34797,(6,0)), EJMTriangleCacheData.mirror 34797⟩,⟨(26774,(0,0)), EJMTriangleCacheData.mirror 26774⟩], ![⟨(6162,(0,0)), EJMSingletonCacheData.mirror 6162⟩,⟨(6162,(0,0)), EJMSingletonCacheData.mirror 6162⟩,⟨(6162,(0,0)), EJMSingletonCacheData.mirror 6162⟩,⟨(6162,(0,0)), EJMSingletonCacheData.mirror 6162⟩,⟨(6162,(0,0)), EJMSingletonCacheData.mirror 6162⟩,⟨(6162,(0,0)), EJMSingletonCacheData.mirror 6162⟩,⟨(6162,(0,0)), EJMSingletonCacheData.mirror 6162⟩,⟨(6162,(0,0)), EJMSingletonCacheData.mirror 6162⟩,⟨(3643,(0,0)), EJMSingletonCacheData.mirror 3643⟩,⟨(3643,(0,0)), EJMSingletonCacheData.mirror 3643⟩,⟨(7163,(0,0)), EJMSingletonCacheData.mirror 7163⟩,⟨(7163,(0,0)), EJMSingletonCacheData.mirror 7163⟩,⟨(5579,(0,0)), EJMSingletonCacheData.mirror 5579⟩,⟨(5579,(0,0)), EJMSingletonCacheData.mirror 5579⟩,⟨(5579,(0,0)), EJMSingletonCacheData.mirror 5579⟩,⟨(5579,(0,0)), EJMSingletonCacheData.mirror 5579⟩]⟩

set_option maxHeartbeats 100000000 in
-- All thirty-two complete cached states and all row fields are compared with the computed prefix.
set_option trace.profiler true in
private theorem exact_fields : checkSame literalCache (zeroCache 14) = true := by
  decide +kernel

theorem literal_cache_exact : literalCache = zeroCache 14 :=
  checked_same _ _ exact_fields

set_option maxHeartbeats 1000000000 in
-- This unchanged actual subtree checks all 545 original tags and their actual contexts.
set_option trace.profiler true in
theorem actual_zero_suffix :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      step lower EJMGlobalScoreSymmetry.dominates scale 7 (zeroPath 14)
      literalCache (zeroPrefix 14) = true := by
  decide +kernel

/-- Rewrite the complete cache equality to recover the exact original computed-cache check. -/
theorem actual_computed_cache_suffix :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      step lower EJMGlobalScoreSymmetry.dominates scale 7 (zeroPath 14)
      (zeroCache 14) (zeroPrefix 14) = true := by
  simpa only [literal_cache_exact] using actual_zero_suffix

#print axioms literal_cache_exact
#print axioms actual_zero_suffix
#print axioms actual_computed_cache_suffix
end D5.S3.Quantum.Entanglement.EJM.EJMMaterializedCacheProbe14
