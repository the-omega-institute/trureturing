/- GID: D5/S3/Quantum/Entanglement/EJM/Replay/Anchor3269/Parts/PreparedEJMOriginalAnchor3269Modular128Part000005
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Replay/Anchor3269/Parts/PreparedEJMOriginalAnchor3269Modular128Part000005
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Replay/Anchor3269/Parts/PreparedEJMOriginalAnchor3269Modular128Part000005.accepted_15_64_439
   digest: Exact original cached replay is checked at the stated prefix occurrences. -/

/- Generated actual-context certificate source; prepared/uncompiled.
No native count, minimum or producer assertion is a Lean premise. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.Replay.Anchor3269.Parts.PreparedEJMOriginalAnchor3269Modular128Part000000
import D5.S3.Quantum.Entanglement.EJM.Replay.Anchor3269.Parts.PreparedEJMOriginalAnchor3269Modular128Part000001
import D5.S3.Quantum.Entanglement.EJM.Replay.Anchor3269.Parts.PreparedEJMOriginalAnchor3269Modular128Part000002
import D5.S3.Quantum.Entanglement.EJM.Replay.Anchor3269.Parts.PreparedEJMOriginalAnchor3269Modular128Part000003
import D5.S3.Quantum.Entanglement.EJM.Replay.Anchor3269.Parts.PreparedEJMOriginalAnchor3269Modular128Part000004
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAnchor3269Modular128
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem accepted_15_64_439 : Accepted 15 64 ⟨439, by decide⟩ := by
  apply assemble 15 64 ⟨439, by decide⟩ (by decide) (![⟨416, by decide⟩,⟨422, by decide⟩,⟨438, by decide⟩,⟨54, by decide⟩]) node_15_439
  intro a
  fin_cases a
  · exact accepted_16_256_416
  · exact accepted_16_257_422
  · exact accepted_16_258_438
  · exact accepted_16_259_54

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMOriginalAnchor3269Modular128
