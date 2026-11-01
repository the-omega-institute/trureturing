/- GID: D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000019
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000019
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000019.node_16_106,D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000019.accepted_16_6_106
   digest: Exact original cached replay is checked at the stated prefix occurrences. -/

/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000015
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000016
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000017
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000018
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_16_106 : EJMOriginalGlobalDAGData.nodes 5 ⟨106, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 16) (![⟨91, by decide⟩,⟨100, by decide⟩,⟨101, by decide⟩,⟨105, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_16_6_106 : Accepted 16 6 ⟨106, by decide⟩ := by
  apply assemble 16 6 ⟨106, by decide⟩ (by decide) (![⟨91, by decide⟩,⟨100, by decide⟩,⟨101, by decide⟩,⟨105, by decide⟩]) node_16_106
  intro a
  fin_cases a
  · exact accepted_17_24_91
  · exact accepted_17_25_100
  · exact accepted_17_26_101
  · exact accepted_17_27_105

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
