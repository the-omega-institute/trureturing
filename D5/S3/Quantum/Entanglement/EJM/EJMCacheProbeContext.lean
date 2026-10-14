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

def checkPath (d : Fin 20) : Bool :=
  match EJMGlobalDAGData.nodes (21 - d.val) (zeroPath d.castSucc) with
  | .split i children => decide (i = d ∧ children 0 = zeroPath d.succ)
  | _ => false

set_option maxHeartbeats 100000000 in
-- The explicit finite kernel domain needs this budget; producer checks are not premises.
set_option trace.profiler true in
theorem zero_path_actual : ∀ d : Fin 20, checkPath d = true := by
  decide +kernel


#print axioms zero_path_actual

end D5.S3.Quantum.Entanglement.EJM.EJMCacheProbe
