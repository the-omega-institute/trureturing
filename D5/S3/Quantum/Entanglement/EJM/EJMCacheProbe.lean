/- Prepared actual-context kernel benchmark. This is not global acceptance
and is not independently delivered. The complete all-branch replay remains
mandatory. The paths and original nodes below are themselves kernel checked. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCacheState
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S0.Certificates.FiniteCachedSymmetryDAGReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

def zeroPrefix (depth : ℕ) : Partial (Fin 20) (Fin 4) :=
  fun g => if g.val < depth then some 0 else none

def zeroCache : ℕ → Cache
  | 0 => initial
  | depth + 1 => step (zeroCache depth) ⟨depth % 20, Nat.mod_lt _ (by decide)⟩ 0

def zeroPath : Fin 21 → Fin EJMGlobalDAGData.Size :=
  ![1646020,1646019,1556252,980935,525047,207629,125624,105947,96271,95226,93669,92906,92460,92370,92235,92193,92174,92167,92163,92161,0]

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
theorem actual_root_proposals :
    EJMTriangleCacheData.checkMirror 41293 = true ∧
    EJMSingletonCacheData.checkMirror 8688 = true ∧
    EJMTriangleCacheData.checkTransitions 41293 = true ∧
    EJMSingletonCacheData.checkTransitions 8688 = true := by
  decide +kernel

def checkPath (d : Fin 20) : Bool :=
  match EJMGlobalDAGData.nodes (21 - d.val) (zeroPath d.castSucc) with
  | .split i children => decide (i = d ∧ children 0 = zeroPath d.succ)
  | _ => false

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
theorem zero_path_actual : ∀ d : Fin 20, checkPath d = true := by
  decide +kernel

set_option maxHeartbeats 10000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
theorem zero_prefix_updates : ∀ d : Fin 20,
    Function.update (zeroPrefix d.val) d (some 0) = zeroPrefix (d.val + 1) := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
theorem actual_first_positive_leaf :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      step lower EJMGlobalScoreSymmetry.dominates scale 1 (zeroPath 20)
      (zeroCache 20) (zeroPrefix 20) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
theorem actual_zero_suffix_18 :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
      step lower EJMGlobalScoreSymmetry.dominates scale 3 (zeroPath 18)
      (zeroCache 18) (zeroPrefix 18) = true := by
  decide +kernel

#print axioms zero_path_actual
#print axioms actual_root_proposals
#print axioms actual_first_positive_leaf
#print axioms actual_zero_suffix_18

end D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe
