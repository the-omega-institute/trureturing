/- Prepared performance sample only, not global acceptance. This checks
the original zero-prefix subtree: depth 14, fuel 7, 545 actual tags.
The complete original DAG and all reached contexts/value branches remain.
No global throughput conclusion follows from this bounded sample alone. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe14
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

set_option maxHeartbeats 1000000000 in
-- This finite original subtree has 545 actual tags, including every value branch.
set_option trace.profiler true in
theorem actual_zero_suffix :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      step lower EJMGlobalScoreSymmetry.dominates scale 7 (zeroPath 14)
      (zeroCache 14) (zeroPrefix 14) = true := by
  decide +kernel

#print axioms actual_zero_suffix
end D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe14
