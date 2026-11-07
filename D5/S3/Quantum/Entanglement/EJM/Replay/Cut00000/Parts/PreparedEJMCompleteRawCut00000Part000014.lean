/- GID: D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000014
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000014
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000014.node_16_77,D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000014.accepted_16_5_77
   digest: Exact original cached replay is checked at the stated prefix occurrences. -/

/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000010
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000011
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000012
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000013
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_16_77 : EJMOriginalGlobalDAGData.nodes 5 ⟨77, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 16) (![⟨64, by decide⟩,⟨67, by decide⟩,⟨76, by decide⟩,⟨29, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_16_5_77 : Accepted 16 5 ⟨77, by decide⟩ := by
  apply assemble 16 5 ⟨77, by decide⟩ (by decide) (![⟨64, by decide⟩,⟨67, by decide⟩,⟨76, by decide⟩,⟨29, by decide⟩]) node_16_77
  intro a
  fin_cases a
  · exact accepted_17_20_64
  · exact accepted_17_21_67
  · exact accepted_17_22_76
  · exact accepted_17_23_29

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
