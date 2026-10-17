/- GID: D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000005
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000005
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000005.node_16_52,D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000005.accepted_16_1_52
   digest: Exact original cached replay is checked at the stated prefix occurrences. -/

/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000001
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000002
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000003
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000004
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_16_52 : EJMOriginalGlobalDAGData.nodes 5 ⟨52, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 16) (![⟨38, by decide⟩,⟨43, by decide⟩,⟨51, by decide⟩,⟨29, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_16_1_52 : Accepted 16 1 ⟨52, by decide⟩ := by
  apply assemble 16 1 ⟨52, by decide⟩ (by decide) (![⟨38, by decide⟩,⟨43, by decide⟩,⟨51, by decide⟩,⟨29, by decide⟩]) node_16_52
  intro a
  fin_cases a
  · exact accepted_17_4_38
  · exact accepted_17_5_43
  · exact accepted_17_6_51
  · exact accepted_17_7_29

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
