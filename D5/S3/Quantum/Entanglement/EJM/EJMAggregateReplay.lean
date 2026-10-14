/- Exact combination of the earned aggregate-cache invariant and the
complete packed-prefix symmetry comparison. This bridge preserves every
original DAG node and all four children; it does not assert acceptance. -/

import D5.S3.Quantum.Entanglement.EJM.EJMAggregateCachePacking
import D5.S3.Quantum.Entanglement.EJM.EJMCompactDominates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Quantum.Entanglement.EJM.EJMAggregateReplay

open EJMAggregateCachePacking (AggregateCache Valid step lower)
open EJMCompactPartial (PackedPartial WellFormed)

def check := EJMCompactDominates.checkFast step lower EJMPartialBoundData.scale

theorem check_eq_original (fuel : ℕ) (index : Fin EJMGlobalDAGData.Size)
    (cache : AggregateCache) (h : Valid cache) (q : PackedPartial)
    (hwell : WellFormed q) (hinv : q.depth + fuel = 21) :
    check fuel index cache q =
      D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
        EJMCacheState.step EJMCacheState.lower EJMGlobalScoreSymmetry.dominates
        EJMPartialBoundData.scale fuel index (EJMCachePacking.decode cache.words)
        (EJMCompactPartial.decode q) := by
  unfold check
  rw [EJMCompactDominates.checkFast_eq_checkPacked step lower _ fuel index cache q hwell hinv]
  exact EJMAggregateCachePacking.replay_eq_original fuel index cache h q hwell hinv

#print axioms check_eq_original

end D5.S3.Quantum.Entanglement.EJM.EJMAggregateReplay
