/- GID: D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000054
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000054
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000054.node_16_287,D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000054.accepted_16_27_287
   digest: Exact original cached replay is checked at the stated prefix occurrences. -/

/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000050
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000051
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000052
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000053
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_16_287 : EJMOriginalGlobalDAGData.nodes 5 ⟨287, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 16) (![⟨258, by decide⟩,⟨268, by decide⟩,⟨285, by decide⟩,⟨286, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_16_27_287 : Accepted 16 27 ⟨287, by decide⟩ := by
  apply assemble 16 27 ⟨287, by decide⟩ (by decide) (![⟨258, by decide⟩,⟨268, by decide⟩,⟨285, by decide⟩,⟨286, by decide⟩]) node_16_287
  intro a
  fin_cases a
  · exact accepted_17_108_258
  · exact accepted_17_109_268
  · exact accepted_17_110_285
  · exact accepted_17_111_286

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
