/- Prepared complete-replay representation bridge. Both representations
retain the exact original rows, actions, unknown coordinates and all four
branches. This bridge supplies no acceptance assertion. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCompactPartial
import D5.S3.Quantum.Entanglement.EJM.EJMCachePacking

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMCompactCachedReplay

open D5.S3.Quantum.Entanglement.EJM.EJMCompactPartial
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)

def actualCheck : Bool :=
  checkPacked EJMGlobalDAGData.nodes EJMCachePacking.step EJMCachePacking.lower
    EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
    21 EJMGlobalDAGData.root EJMCachePacking.initial actualPacked

theorem replay_eq_original
    (fuel : ℕ) (index : Fin EJMGlobalDAGData.Size)
    (cache : EJMCachePacking.PackedCache) (q : PackedPartial)
    (hwell : WellFormed q) (hinv : q.depth + fuel = 21) :
    checkPacked EJMGlobalDAGData.nodes EJMCachePacking.step EJMCachePacking.lower
        EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
        fuel index cache q =
      check EJMGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
        EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
        fuel index (EJMCachePacking.decode cache) (decode q) := by
  exact (checkPacked_eq_original EJMCachePacking.step EJMCachePacking.lower
    fuel index cache q hwell hinv).trans
    (EJMCachePacking.check_decode EJMGlobalDAGData.nodes
      EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
      fuel index cache (decode q))

theorem actualCheck_eq_original :
    actualCheck =
      check EJMGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
        EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
        21 EJMGlobalDAGData.root EJMCacheState.initial (fun _ => none) := by
  unfold actualCheck
  rw [replay_eq_original 21 EJMGlobalDAGData.root EJMCachePacking.initial
    actualPacked actualPacked_wellFormed actualPacked_invariant,
    EJMCachePacking.decode_initial, actualPacked_decode]

#print axioms replay_eq_original
#print axioms actualCheck_eq_original

end D5.S3.Quantum.Entanglement.EJM.EJMCompactCachedReplay
