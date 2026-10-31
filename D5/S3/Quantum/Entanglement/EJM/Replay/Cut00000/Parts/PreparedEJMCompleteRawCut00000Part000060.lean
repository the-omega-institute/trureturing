/- GID: D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000060
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000060
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000060.node_13_292,D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000060.accepted_13_0_292
   digest: Exact original cached replay is checked at the stated prefix occurrences. -/

/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000024
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000057
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000058
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000059
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_13_292 : EJMOriginalGlobalDAGData.nodes 8 ⟨292, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 13) (![⟨110, by decide⟩,⟨289, by decide⟩,⟨290, by decide⟩,⟨291, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_13_0_292 : Accepted 13 0 ⟨292, by decide⟩ := by
  apply assemble 13 0 ⟨292, by decide⟩ (by decide) (![⟨110, by decide⟩,⟨289, by decide⟩,⟨290, by decide⟩,⟨291, by decide⟩]) node_13_292
  intro a
  fin_cases a
  · exact accepted_14_0_110
  · exact accepted_14_1_289
  · exact accepted_14_2_290
  · exact accepted_14_3_291

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
