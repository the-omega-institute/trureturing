/- GID: D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000008
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000008
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000008.node_15_55,D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000008.accepted_15_0_55
   digest: Exact original cached replay is checked at the stated prefix occurrences. -/

/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000000
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000005
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000006
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000007
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_15_55 : EJMOriginalGlobalDAGData.nodes 6 ⟨55, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 15) (![⟨30, by decide⟩,⟨52, by decide⟩,⟨53, by decide⟩,⟨54, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_15_0_55 : Accepted 15 0 ⟨55, by decide⟩ := by
  apply assemble 15 0 ⟨55, by decide⟩ (by decide) (![⟨30, by decide⟩,⟨52, by decide⟩,⟨53, by decide⟩,⟨54, by decide⟩]) node_15_55
  intro a
  fin_cases a
  · exact accepted_16_0_30
  · exact accepted_16_1_52
  · exact accepted_16_2_53
  · exact accepted_16_3_54

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
