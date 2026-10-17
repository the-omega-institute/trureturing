/- GID: D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000032
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000032
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000032.accepted_17_85_159
   digest: Exact original cached replay is checked at the stated prefix occurrences. -/

/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

set_option trace.profiler true in
theorem accepted_17_85_159 : Accepted 17 85 ⟨159, by decide⟩ := by
  change D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check
    EJMOriginalGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
    EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
    4 ⟨159, by decide⟩ (prefixCache 17 85)
    (prefixPartial 17 85) = true
  decide +kernel

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
