/- GID: D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000024
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000024
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000024.node_14_110,D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000024.accepted_14_0_110
   digest: Exact original cached replay is checked at the stated prefix occurrences. -/

/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000008
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000021
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000022
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000023
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_14_110 : EJMOriginalGlobalDAGData.nodes 7 ⟨110, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 14) (![⟨55, by decide⟩,⟨107, by decide⟩,⟨108, by decide⟩,⟨109, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_14_0_110 : Accepted 14 0 ⟨110, by decide⟩ := by
  apply assemble 14 0 ⟨110, by decide⟩ (by decide) (![⟨55, by decide⟩,⟨107, by decide⟩,⟨108, by decide⟩,⟨109, by decide⟩]) node_14_110
  intro a
  fin_cases a
  · exact accepted_15_0_55
  · exact accepted_15_1_107
  · exact accepted_15_2_108
  · exact accepted_15_3_109

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
