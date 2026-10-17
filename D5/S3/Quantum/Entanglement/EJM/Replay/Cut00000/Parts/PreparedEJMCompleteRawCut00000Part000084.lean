/- GID: D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000084
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000084
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000084.node_12_415,D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000084.accepted_12_0_415
   digest: Exact original cached replay is checked at the stated prefix occurrences. -/

/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000060
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000081
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000082
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000083
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_12_415 : EJMOriginalGlobalDAGData.nodes 9 ⟨415, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 12) (![⟨292, by decide⟩,⟨412, by decide⟩,⟨413, by decide⟩,⟨414, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_12_0_415 : Accepted 12 0 ⟨415, by decide⟩ := by
  apply assemble 12 0 ⟨415, by decide⟩ (by decide) (![⟨292, by decide⟩,⟨412, by decide⟩,⟨413, by decide⟩,⟨414, by decide⟩]) node_12_415
  intro a
  fin_cases a
  · exact accepted_13_0_292
  · exact accepted_13_1_412
  · exact accepted_13_2_413
  · exact accepted_13_3_414

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
