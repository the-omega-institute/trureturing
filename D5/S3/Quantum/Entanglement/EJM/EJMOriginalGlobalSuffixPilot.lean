/- Transient exact original-suffix cost probe, not yet compiled.
The original initial cache and every actual prefix update are retained.
This suffix alone asserts no universal score bound or locality exclusion. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalCachedGlobalReplay
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.EJMOriginalGlobalSuffixPilot
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (initial)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def prefix : Fin 15 → Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def cache : Cache :=
  (List.finRange 15).foldl
    (fun cache i => step cache ⟨i.val, by have h := i.isLt; omega⟩ (prefix i))
    initial
private def partial : Partial (Fin 20) (Fin 4) := fun g =>
  if h : g.val < 15 then some (prefix ⟨g.val, h⟩) else none

set_option trace.profiler true in
private theorem suffix_accepted :
    check EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨55, by decide⟩ cache partial = true := by
  decide +kernel

#print axioms suffix_accepted
end D5.S3.Quantum.Entanglement.EJM.EJMOriginalGlobalSuffixPilot
