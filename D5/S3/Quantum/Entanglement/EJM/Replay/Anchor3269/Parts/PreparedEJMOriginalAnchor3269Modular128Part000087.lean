/- GID: D5/S3/Quantum/Entanglement/EJM/Replay/Anchor3269/Parts/PreparedEJMOriginalAnchor3269Modular128Part000087
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Replay/Anchor3269/Parts/PreparedEJMOriginalAnchor3269Modular128Part000087
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Replay/Anchor3269/Parts/PreparedEJMOriginalAnchor3269Modular128Part000087.accepted_16_302_670
   digest: Exact original cached replay is checked at the stated prefix occurrences. -/

/- Generated actual-context certificate source; prepared/uncompiled.
No native count, minimum or producer assertion is a Lean premise. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAnchor3269Modular128
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem accepted_16_302_670 : Accepted 16 302 ⟨670, by decide⟩ := by
  change D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check
    EJMOriginalGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
    EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
    5 ⟨670, by decide⟩ (prefixCache 16 302)
    (prefixPartial 16 302) = true
  decide +kernel

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAnchor3269Modular128
